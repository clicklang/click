//! Exact wide equality premises indexed by shallow operand identity.
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
use crate::kernel::{
    Address, ConditionTerm, MachineIntegerType, MachineOperandView, MachineTerm, Proposition,
};
use crate::persistent::{PersistentComponents, PersistentMap, PersistentSet};

/// Reachability in the store's numeric-address graph. An equality joins two
/// word operands, and each explicit address operand joins its object bucket.
/// Keeping the two kinds of node distinct preserves the difference between
/// numeric equality and possible byte overlap through another displacement.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct NumericAddressConnectivity {
    operands: PersistentMap<Key, u64>,
    objects: PersistentMap<Address, u64>,
    components: PersistentComponents<u64>,
    next_id: u64,
}

impl NumericAddressConnectivity {
    pub(in crate::kernel) fn record(&mut self, endpoints: [(&Key, &MachineTerm); 2]) {
        let [left, right] = endpoints.map(|(key, term)| {
            let operand = Self::node(&mut self.operands, &mut self.next_id, key);
            if let Some(address) = term.address_pointer() {
                let bucket = crate::kernel::assumptions::parameter_alias_bucket(address);
                let object = Self::node(&mut self.objects, &mut self.next_id, &bucket);
                self.components.join(&operand, &object);
            }
            operand
        });
        self.components.join(&left, &right);
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

    pub(in crate::kernel) fn connected(&self, left: &Address, right: &Address) -> bool {
        use crate::kernel::assumptions::parameter_alias_bucket;
        let Some(left) = self.objects.get(&parameter_alias_bucket(left)) else {
            return false;
        };
        self.objects
            .get(&parameter_alias_bucket(right))
            .is_some_and(|right| self.components.root(left) == self.components.root(right))
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
