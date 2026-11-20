//! Exact wide equality premises indexed by shallow operand identity.
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{
    Address, AddressBase, AddressOffset, ConditionTerm, MachineIntegerType, MachineOperandView,
    MachineTerm, Proposition,
};
use crate::persistent::{PersistentComponents, PersistentMap, PersistentSet};
use std::collections::BTreeSet;

/// Reachability in the store's numeric-address graph. An equality joins two
/// word operands, and each explicit address operand joins its object bucket.
/// Keeping the two kinds of node distinct preserves the difference between
/// numeric equality and possible byte overlap through another displacement.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct NumericAddressConnectivity {
    operands: PersistentMap<Key, u64>,
    other_objects: PersistentMap<Address, u64>,
    owner_forest: NumericAddressForest,
    next_id: u64,
    has_variable_endpoint: bool,
}

/// The paths through the numeric union forest use only numeric IDs. Keeping
/// variable-based owner addresses separate lets a memory cache hold this
/// snapshot without retaining read operands that may name the cache itself.
#[derive(Clone, Debug, Default)]
struct NumericAddressForest {
    objects: PersistentMap<Address, u64>,
    components: PersistentComponents<u64>,
}

impl NumericAddressConnectivity {
    pub(in crate::kernel) fn record(&mut self, endpoints: [(&Key, &MachineTerm); 2]) {
        let [left, right] = endpoints.map(|(key, term)| {
            self.has_variable_endpoint |= key.operand_view().variable().is_some();
            let operand = Self::node(&mut self.operands, &mut self.next_id, key);
            if let Some(address) = term.address_pointer() {
                let bucket = crate::kernel::assumptions::parameter_alias_bucket(address);
                let objects = if Self::can_be_owner(&bucket) {
                    &mut self.owner_forest.objects
                } else {
                    &mut self.other_objects
                };
                let object = Self::node(objects, &mut self.next_id, &bucket);
                self.owner_forest.components.join(&operand, &object);
            }
            operand
        });
        self.owner_forest.components.join(&left, &right);
    }

    fn can_be_owner(bucket: &Address) -> bool {
        bucket.base == AddressBase::ExternalArgument
            && match &bucket.offset {
                AddressOffset::Variable(_) => true,
                AddressOffset::Int32Scaled { value, .. } => {
                    value.operand_view().variable().is_some()
                }
                _ => false,
            }
    }

    fn node<K: Ord + Clone>(nodes: &mut PersistentMap<K, u64>, next_id: &mut u64, key: &K) -> u64 {
        if let Some(id) = nodes.get(key) {
            return *id;
        }
        let id = *next_id;
        *next_id += 1;
        nodes.insert(key.clone(), id);
        id
    }

    /// A raw variable equality can stand for a parameter address without
    /// naming its object bucket. Preserve the conservative store fallback
    /// when such an endpoint may be present.
    pub(super) fn has_raw_store_alias_endpoints(&self) -> bool {
        self.has_variable_endpoint
    }

    pub(in crate::kernel) fn connected(&self, left: &Address, right: &Address) -> bool {
        use crate::kernel::assumptions::parameter_alias_bucket;
        let node = |address| {
            let bucket = parameter_alias_bucket(address);
            self.owner_forest
                .objects
                .get(&bucket)
                .or_else(|| self.other_objects.get(&bucket))
        };
        let Some(left) = node(left) else {
            return false;
        };
        let components = &self.owner_forest.components;
        node(right).is_some_and(|right| components.root(left) == components.root(right))
    }
}

impl NumericAddressForest {
    fn component(&self, bucket: &Address) -> Option<u64> {
        self.objects
            .get(bucket)
            .map(|node| *self.components.root(node))
    }
}

/// The part of the numeric union forest that leads to populated cache
/// owners. Empty branches have no entries. The forest itself remains in
/// the fact store, and the snapshot supplies no additional premises.
#[derive(Clone, Default)]
pub(in crate::kernel) struct NumericAddressOwners {
    forest: NumericAddressForest,
    populated: PersistentMap<u64, PopulatedOwners>,
}

#[derive(Clone, Default)]
struct PopulatedOwners {
    owner: Option<Address>,
    children: PersistentSet<u64>,
}

impl PopulatedOwners {
    fn is_empty(&self) -> bool {
        self.owner.is_none() && self.children.is_empty()
    }

    fn set_child(&mut self, child: u64, present: bool) {
        self.children = if present {
            self.children.with_value(child)
        } else {
            self.children.without_value(&child)
        };
    }
}

impl NumericAddressOwners {
    pub(in crate::kernel) fn new(connectivity: &NumericAddressConnectivity) -> Self {
        Self {
            forest: connectivity.owner_forest.clone(),
            populated: Default::default(),
        }
    }

    pub(in crate::kernel) fn owners(&self, base: &Address) -> Option<BTreeSet<Address>> {
        let root = self.forest.component(base)?;
        let mut owners = BTreeSet::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(bucket) = self.populated.get(&node) {
                owners.extend(bucket.owner.iter().cloned());
                pending.extend(bucket.children.iter().copied());
            }
        }
        Some(owners)
    }

    pub(in crate::kernel) fn update_owner(&mut self, owner: Address, present: bool) {
        if let Some(&node) = self.forest.objects.get(&owner) {
            self.set_owner(node, present.then_some(owner));
        }
    }

    fn set_owner(&mut self, node: u64, owner: Option<Address>) {
        let mut bucket = self.populated.get(&node).cloned().unwrap_or_default();
        if bucket.owner != owner {
            bucket.owner = owner;
            self.set_node(node, bucket);
        }
    }

    fn set_child(&mut self, parent: u64, child: u64, present: bool) {
        let mut bucket = self.populated.get(&parent).cloned().unwrap_or_default();
        if bucket.children.contains(&child) != present {
            bucket.set_child(child, present);
            self.set_node(parent, bucket);
        }
    }

    /// Propagate an empty/nonempty transition along the existing union links.
    /// The height is logarithmic by union by size.
    fn set_node(&mut self, mut node: u64, mut bucket: PopulatedOwners) {
        loop {
            crate::instrumentation::record_deterministic_work(1);
            let was_present = self.populated.contains_key(&node);
            let present = !bucket.is_empty();
            if present {
                self.populated.insert(node, bucket);
            } else {
                self.populated.remove(&node);
            }
            if was_present == present {
                return;
            }
            let Some(&parent) = self.forest.components.parent(&node) else {
                return;
            };
            bucket = self.populated.get(&parent).cloned().unwrap_or_default();
            if bucket.children.contains(&node) == present {
                return;
            }
            bucket.set_child(node, present);
            node = parent;
        }
    }

    /// Detach changed bindings and links under the old forest, then attach
    /// them under the new forest. A union or a fork with a different parent
    /// changes only links, without inspecting the owners below those links.
    pub(in crate::kernel) fn refresh(
        &mut self,
        newer: &NumericAddressConnectivity,
        populated: impl Fn(&Address) -> bool,
    ) {
        let newer = &newer.owner_forest;
        let older = self.forest.clone();
        let mut new_owners = Vec::new();
        for (owner, old_node, new_node) in older.objects.diff(&newer.objects) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(&node) = old_node {
                self.set_owner(node, None);
            }
            if let Some(&node) = new_node
                && populated(owner)
            {
                new_owners.push((node, owner.clone()));
            }
        }
        let mut new_links = Vec::new();
        for (node, old_parent, new_parent) in older.components.parent_changes(&newer.components) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(&parent) = old_parent {
                self.set_child(parent, *node, false);
            }
            if let Some(&parent) = new_parent {
                new_links.push((parent, *node));
            }
        }
        self.forest = newer.clone();
        for (node, owner) in new_owners {
            self.set_owner(node, Some(owner));
        }
        for (parent, node) in new_links {
            if self.populated.contains_key(&node) {
                self.set_child(parent, node, true);
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct WideEqualitySources {
    endpoints: PersistentMap<Key, PersistentMap<Key, PersistentSet<Proposition>>>,
}

impl WideEqualitySources {
    pub(in crate::kernel) fn adjust(
        &mut self,
        condition: &ConditionTerm,
        truth: bool,
        admitted_endpoints: Option<&(super::MachineAtom, super::MachineAtom)>,
    ) {
        let Some(view) = comparison_view(condition, truth) else {
            return;
        };
        if view.relation != Relation::Equal || view.format.format().bits() != 64 {
            return;
        }
        let operand_key = |operand: MachineOperandView<'_>,
                           admitted: Option<&super::MachineAtom>| {
            if let MachineOperandView::Legacy(written) = operand
                && let Some(admitted) = admitted
                && matches!(admitted.operand_view(), MachineOperandView::Shared(_))
                && admitted.retains_written(written)
            {
                // Native equality admission already imported this exact
                // endpoint. Its canonical form may differ, so reuse it only
                // when it retained the same explicit written operand.
                Key::Shared(admitted.clone())
            } else {
                Key::for_format(MachineIntegerType::UInt64, operand)
            }
        };
        let left = operand_key(
            view.operands[0].operand_view(),
            admitted_endpoints.map(|ends| &ends.0),
        );
        let right = operand_key(
            view.operands[1].operand_view(),
            admitted_endpoints.map(|ends| &ends.1),
        );
        let source = Proposition::condition_is(condition.clone(), truth);
        for (own, other) in [(&left, &right), (&right, &left)] {
            let mut neighbors = self.endpoints.get(own).cloned().unwrap_or_default();
            let sources = neighbors.get(other).cloned().unwrap_or_default();
            let sources = sources.with_value(source.clone());
            if sources.is_empty() {
                neighbors.remove(other);
            } else {
                neighbors.insert(other.clone(), sources);
            }
            if neighbors.is_empty() {
                self.endpoints.remove(own);
            } else {
                self.endpoints.insert(own.clone(), neighbors);
            }
        }
    }

    pub(in crate::kernel) fn neighbors(
        &self,
        operand: MachineOperandView<'_>,
    ) -> impl Iterator<Item = (MachineOperandView<'_>, &Proposition)> {
        self.endpoints
            .get(&Key::for_format(MachineIntegerType::UInt64, operand))
            .into_iter()
            .flat_map(|neighbors| neighbors.iter())
            .filter_map(|(other, sources)| {
                sources
                    .iter()
                    .next()
                    .map(|source| (other.operand_view(), source))
            })
    }

    pub(in crate::kernel) fn shares_root_with(&self, other: &Self) -> bool {
        self.endpoints.shares_root_with(&other.endpoints)
    }
}
