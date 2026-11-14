use super::*;

fn read_pointer(id: u64) -> PointerValue {
    let memory = crate::kernel::intern_memory(Memory::new());
    let cell = Pointer::symbolic(Variable(id));
    PointerValue::from_read(
        Pointer::loaded_value(&memory, &cell),
        ProgramType::Int32Pointer,
        &memory,
        &cell,
    )
}

#[test]
fn a_full_pointer_equality_connects_a_read_extent_to_owned_root_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(981_000),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored = PointerValue::new(base.clone(), ProgramType::Int32Pointer);
    let read = read_pointer(981_001);
    let held = MemoryRange::new(base.clone(), 0u32.into(), 8u32.into());
    let before = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(read.pointer().clone(), base),
        true,
    );
    assert!(!before.access_designations_match(read.access_designation(), &held));
    let after = before.clone().assume_condition(
        ConditionTerm::pointer_value_equal(read.clone(), stored),
        true,
    );
    assert!(after.access_designations_match(read.access_designation(), &held));
    assert!(!before.access_designations_match(read.access_designation(), &held));
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(held));
    resources.synchronize_memory_equalities(&after);
    let required = ResourceFact::own_memory(
        MemoryRange::new(read.pointer().clone(), 0u32.into(), 8u32.into())
            .with_pointer_carrier(&read),
    );
    assert!(resources.satisfies_fact(&required, &after));
    assert!(
        resources
            .without_fact_incrementally(&required, &after)
            .is_some()
    );
}

#[test]
fn a_known_subobject_extent_does_not_grant_root_storage_access() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(981_002),
        offset: PointerOffsetTerm::Constant(0),
    };
    let bounded = PointerValue::new(base.clone(), ProgramType::Int32Pointer).with_extent(Some(
        SubobjectExtent {
            start: base.clone(),
            width: 4u32.into(),
        },
    ));
    let read = read_pointer(981_003);
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_value_equal(read.clone(), bounded),
        true,
    );
    let held = MemoryRange::new(base, 0u32.into(), 8u32.into());
    assert!(facts.designations_equal(read.designation(), &held.designation));
    assert!(
        !facts
            .equality_graph
            .opaque_extent_is_root(read.opaque_extent().unwrap())
    );
    assert!(!facts.access_designations_match(read.access_designation(), &held));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/root_extents.rs");
}
