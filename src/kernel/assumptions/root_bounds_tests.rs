use super::*;

fn read_pointer(id: u64) -> OldPointer {
    let memory = crate::kernel::intern_memory(SymbolicMemory::new());
    let cell = Address::symbolic(Variable(id));
    OldPointer::from_read(
        Address::loaded_value(&memory, &cell),
        ProgramType::Int32Pointer,
        &memory,
        &cell,
    )
}

#[test]
fn a_full_pointer_equality_connects_a_read_bounds_to_owned_root_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Address {
        base: AddressBase::Heap(981_000),
        offset: AddressOffset::Constant(0),
    };
    let stored = OldPointer::new(base.clone(), ProgramType::Int32Pointer);
    let read = read_pointer(981_001);
    let held = MemoryRange::new(base.clone(), 0u32.into(), 8u32.into());
    let before = PureFactContext::new().assume_condition(
        ConditionTerm::address_equal(read.address().clone(), base),
        true,
    );
    assert!(!before.access_provenance_match(read.access_provenance(), &held));
    let after = before
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(read.clone(), stored), true);
    assert!(after.access_provenance_match(read.access_provenance(), &held));
    assert!(!before.access_provenance_match(read.access_provenance(), &held));
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(held));
    resources.synchronize_memory_equalities(&after);
    let required = ResourceFact::own_memory(
        MemoryRange::new(read.address().clone(), 0u32.into(), 8u32.into())
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
fn a_known_subobject_bounds_does_not_grant_root_storage_access() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Address {
        base: AddressBase::Heap(981_002),
        offset: AddressOffset::Constant(0),
    };
    let bounded = OldPointer::new(base.clone(), ProgramType::Int32Pointer).with_bounds(Some(
        SubobjectBounds {
            start: base.clone(),
            width: 4u32.into(),
        },
    ));
    let read = read_pointer(981_003);
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(read.clone(), bounded), true);
    let held = MemoryRange::new(base, 0u32.into(), 8u32.into());
    assert!(facts.provenance_equal(read.provenance(), &held.provenance));
    assert!(
        !facts
            .equality_graph
            .bounds_owner_is_root(read.bounds_owner().unwrap())
    );
    assert!(!facts.access_provenance_match(read.access_provenance(), &held));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/root_bounds.rs");
}
