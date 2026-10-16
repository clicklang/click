//! Value-origin equality. Address congruence must never enter this index.
use super::CPointerValue;
use crate::persistent::PersistentMap;
use std::collections::BTreeSet;

/// Persistent union by size, with exact edge support for scoped withdrawal.
/// Insertion touches two root paths. Withdrawal rebuilds only the affected
/// component, never the ambient address graph or unrelated value origins.
#[derive(Clone, Debug)]
pub(super) struct ValueClasses<K: Ord> {
    parents: PersistentMap<K, K>,
    sizes: PersistentMap<K, usize>,
    edges: PersistentMap<K, PersistentMap<K, usize>>,
    representative: PersistentMap<K, K>,
}
impl<K: Ord> Default for ValueClasses<K> {
    fn default() -> Self {
        Self {
            parents: Default::default(),
            sizes: Default::default(),
            edges: Default::default(),
            representative: Default::default(),
        }
    }
}
impl<K: Ord + Clone> ValueClasses<K> {
    fn root(&self, value: &K) -> K {
        let mut root = value;
        while let Some(parent) = self.parents.get(root) {
            crate::instrumentation::record_deterministic_work(1);
            root = parent;
        }
        root.clone()
    }
    pub(super) fn equal(&self, left: &K, right: &K) -> bool {
        left == right || self.root(left) == self.root(right)
    }
    pub(super) fn representative(&self, value: &K) -> K {
        self.representative
            .get(&self.root(value))
            .unwrap_or(value)
            .clone()
    }
    pub(super) fn direct_aliases(&self, value: &K) -> impl Iterator<Item = &K> {
        self.edges
            .get(value)
            .into_iter()
            .flat_map(|neighbors| neighbors.iter().map(|(key, _)| key))
    }
    fn join(&mut self, left: &K, right: &K, prefer: impl Fn(&K, &K) -> K) {
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return;
        }
        let mut a = self.sizes.get(&left).copied().unwrap_or(1);
        let mut b = self.sizes.get(&right).copied().unwrap_or(1);
        if a < b {
            std::mem::swap(&mut left, &mut right);
            std::mem::swap(&mut a, &mut b);
        }
        let value = prefer(&self.representative(&left), &self.representative(&right));
        self.parents = self.parents.with_inserted(right.clone(), left.clone());
        self.sizes = self
            .sizes
            .without_key(&right)
            .with_inserted(left.clone(), a + b);
        self.representative = self
            .representative
            .without_key(&right)
            .with_inserted(left, value);
    }
    pub(super) fn insert(&mut self, left: &K, right: &K, prefer: impl Fn(&K, &K) -> K) {
        if left == right {
            return;
        }
        for (a, b) in [(left, right), (right, left)] {
            let neighbors = self.edges.get(a).cloned().unwrap_or_default();
            let count = neighbors.get(b).copied().unwrap_or(0);
            self.edges = self
                .edges
                .with_inserted(a.clone(), neighbors.with_inserted(b.clone(), count + 1));
        }
        self.join(left, right, prefer);
    }
    pub(super) fn remove(&mut self, left: &K, right: &K, prefer: impl Fn(&K, &K) -> K + Copy) {
        if left == right {
            return;
        }
        let Some(count) = self.edges.get(left).and_then(|n| n.get(right)).copied() else {
            return;
        };
        for (a, b) in [(left, right), (right, left)] {
            let neighbors = self.edges.get(a).cloned().unwrap_or_default();
            let neighbors = if count == 1 {
                neighbors.without_key(b)
            } else {
                neighbors.with_inserted(b.clone(), count - 1)
            };
            self.edges = if neighbors.is_empty() {
                self.edges.without_key(a)
            } else {
                self.edges.with_inserted(a.clone(), neighbors)
            };
        }
        if count > 1 {
            return;
        }
        let mut component = BTreeSet::new();
        let mut pending = vec![left.clone(), right.clone()];
        while let Some(value) = pending.pop() {
            if !component.insert(value.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(neighbors) = self.edges.get(&value) {
                pending.extend(neighbors.iter().map(|(key, _)| key.clone()));
            }
        }
        for value in &component {
            self.parents = self.parents.without_key(value);
            self.sizes = self.sizes.without_key(value);
            self.representative = self.representative.without_key(value);
        }
        for value in component {
            let neighbors = self.edges.get(&value).cloned().unwrap_or_default();
            for (neighbor, _) in neighbors.iter() {
                self.join(&value, neighbor, prefer);
            }
        }
    }
}

pub(super) fn prefer_pointer(left: &CPointerValue, right: &CPointerValue) -> CPointerValue {
    // A contract supplies the designation of an opaque incoming value. Its
    // explicit subobject boundary takes precedence over an unknown extent.
    if !left.extent_is_known() && right.extent_is_known() {
        right.clone()
    } else {
        left.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::*;

    fn value(id: u64) -> CPointerValue {
        CPointerValue::new(Pointer::symbolic(Variable(id)), CType::Int32Pointer)
    }
    fn equality(a: &CPointerValue, b: &CPointerValue) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(a.clone()), Box::new(b.clone())),
            true,
        )
    }
    #[test]
    fn only_true_full_pointer_equalities_supply_numeric_index_equalities() {
        let a = Bitvector32Term::Variable(Variable(809_998));
        let b = Bitvector32Term::Variable(Variable(809_999));
        let pointer = |index| {
            CPointerValue::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(index, 4),
                },
                CType::Int32Pointer,
            )
        };
        let equality = ConditionTerm::PointerValueEqual(
            Box::new(pointer(a.clone())),
            Box::new(pointer(b.clone())),
        );
        let context = PureFactContext::new().assume_condition(equality.clone(), true);
        assert!(context.int32_values_known_equal(&a, &b));
        let unequal = PureFactContext::new().assume_condition(equality, false);
        assert!(!unequal.int32_values_known_equal(&a, &b));
    }

    #[test]
    fn a_proven_null_address_denotes_the_unique_null_value() {
        let pointer = value(810_000);
        let null = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
        let empty = PureFactContext::new();
        assert!(!empty.pointer_designations_match(&pointer, &null));
        let context = empty.assume_condition(
            ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
            true,
        );
        assert!(context.pointer_designations_match(&pointer, &null));
        assert!(crate::kernel::resource_arguments_proven_equal(
            &CValue::Pointer(pointer).into(),
            &CValue::Pointer(null).into(),
            &context,
        ));
    }

    #[test]
    fn address_equality_preserves_memory_aliasing_without_granting_designation() {
        let a = value(810_001);
        let b = value(810_002);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::from_pointer_value(&b, 0u32.into(), 1u32.into(), 4),
        ));
        assert!(context.pointers_known_equal(a.pointer(), b.pointer()));
        assert!(resources.permits_memory_read(a.pointer(), 4, &context));
        assert!(!resources.permits_designated_memory_read(
            a.pointer(),
            Some(a.access_designation()),
            4,
            &context
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    a.pointer(),
                    Some(a.access_designation()),
                    4,
                    &context
                )
                .is_none()
        );
        let linked = context.clone().assume_proposition(equality(&a, &b));
        assert!(resources.permits_designated_memory_read(
            a.pointer(),
            Some(a.access_designation()),
            4,
            &linked
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    a.pointer(),
                    Some(a.access_designation()),
                    4,
                    &linked
                )
                .is_some()
        );
        let withdrawn = linked.without_exact_fact(&equality(&a, &b));
        assert!(withdrawn.pointers_known_equal(a.pointer(), b.pointer()));
        assert!(!resources.permits_designated_memory_read(
            a.pointer(),
            Some(a.access_designation()),
            4,
            &withdrawn
        ));
    }
    #[test]
    fn equality_of_widened_views_does_not_widen_the_original_input() {
        let input = value(815_001);
        let parent = value(815_002);
        let byte_view = input.clone().with_root_extent();
        let parent_view = parent.clone().with_root_extent();
        let context = PureFactContext::new().assume_proposition(equality(&byte_view, &parent_view));
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::from_pointer_value(&parent, 0u32.into(), 2u32.into(), 4),
        ));
        assert!(context.designations_equal(input.designation(), parent.designation()));
        assert!(!resources.permits_designated_memory_read(
            input.pointer(),
            Some(input.access_designation()),
            4,
            &context
        ));
        assert!(resources.permits_designated_memory_read(
            byte_view.pointer(),
            Some(byte_view.access_designation()),
            4,
            &context
        ));
        let split = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::from_pointer_value(
                &input,
                0u32.into(),
                1u32.into(),
                4,
            )))
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::from_pointer_value(
                &parent,
                1u32.into(),
                2u32.into(),
                4,
            )))
            .normalized(&context);
        let sibling = input.pointer().offset_by_bytes(4);
        assert!(!split.permits_designated_memory_read(
            &sibling,
            Some(input.access_designation()),
            4,
            &context
        ));
        let selected = byte_view.with_extent(Some(SubobjectExtent {
            start: input.pointer().clone(),
            width: 4,
        }));
        let selected_resources =
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::from_pointer_value(&selected, 0u32.into(), 1u32.into(), 4),
            ));
        assert!(!selected_resources.permits_designated_memory_read(
            input.pointer(),
            Some(input.access_designation()),
            4,
            &context
        ));
    }

    #[test]
    fn origin_support_handles_cycles_reverse_edges_and_branch_withdrawal() {
        let a = value(820_001);
        let b = value(820_002);
        let c = value(820_003);
        let ab = equality(&a, &b);
        let ba = equality(&b, &a);
        let bc = equality(&b, &c);
        let context = PureFactContext::new()
            .assume_proposition(ab.clone())
            .assume_proposition(ba.clone())
            .assume_proposition(bc.clone());
        let without_ab = context.clone().without_exact_fact(&ab);
        assert!(without_ab.designations_equal(a.designation(), c.designation()));
        let without_both = without_ab.without_exact_fact(&ba);
        assert!(!without_both.designations_equal(a.designation(), c.designation()));
        assert!(without_both.designations_equal(b.designation(), c.designation()));
        assert!(context.designations_equal(a.designation(), c.designation()));
    }
    #[test]
    fn a_narrowed_read_does_not_narrow_its_enclosing_pointer() {
        let parent = value(824_001);
        let member = parent.clone().with_extent(Some(SubobjectExtent {
            start: parent.pointer().clone(),
            width: 4,
        }));
        let snapshot = crate::kernel::intern_c_memory(CMemory::new());
        let cell = Pointer::symbolic(Variable(824_002));
        let read_address = Pointer::symbolic(Variable(824_003));
        let read = CPointerValue::from_read(read_address, CType::Int32Pointer, &snapshot, &cell);
        let context = PureFactContext::new().assume_proposition(equality(&read, &member));
        assert!(context.pointer_value_at_entry(&read).extent().is_some());
        assert!(context.pointer_value_at_entry(&parent).extent().is_none());
        assert!(!context.contains_known(&equality(&parent, &member)));
        assert!(!context.pointer_designations_match(&parent, &read));
    }

    #[test]
    fn equal_storage_addresses_preserve_a_complete_pointer_reads_designation() {
        let a = value(825_001);
        let b = value(825_002);
        let snapshot = crate::kernel::intern_c_memory(CMemory::new());
        let x = CPointerValue::from_read(
            Pointer::symbolic(Variable(825_003)),
            CType::Int32Pointer,
            &snapshot,
            a.pointer(),
        );
        let y = CPointerValue::from_read(
            Pointer::symbolic(Variable(825_004)),
            CType::Int32Pointer,
            &snapshot,
            b.pointer(),
        );
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        assert!(!context.designations_equal(a.designation(), b.designation()));
        assert!(context.designations_equal(x.designation(), y.designation()));
    }

    #[test]
    fn pointer_value_equality_combines_with_a_scalar_offset_equality() {
        let a = value(830_001);
        let b = value(830_002);
        let offset = Bitvector32Term::Variable(Variable(830_003));
        let facts = [
            equality(&a, &b),
            Proposition::ConditionIs(ConditionTerm::equal(offset.clone(), 0u32.into()), true),
        ];
        let context = facts.iter().fold(PureFactContext::new(), |c, f| {
            c.assume_proposition(f.clone())
        });
        let displaced = a.clone().with_address(
            a.pointer()
                .offset_by_typed_elements(offset, 4, false, false),
        );
        let goal = equality(&displaced, &b);
        assert!(context.pointer_designations_match(&displaced, &b));
        assert!(context.pointers_known_equal(displaced.pointer(), b.pointer()));
        assert!(context.contains_known(&goal));
        let proof_facts = crate::kernel::proof::ProofFacts::from_ordered(&facts);
        assert!(
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                &[],
                &proof_facts
            )
            .is_ok()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/pointer_designations/tests.rs");
}
