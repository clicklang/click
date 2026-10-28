use super::*;

#[test]
fn token_discovery_follows_a_producer_defined_pointer_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let field = Pointer {
        block: "local:field".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = Pointer::symbolic(Variable(976_000));
    let read = Pointer::loaded_value(&memory, &field);
    let facts = PureFactContext::new();
    facts
        .equality_graph
        .register_pointer_read_definition(&value, &memory, &field);
    let wrap = |pointer| CPointerValue::from_read(pointer, CType::Int32Pointer, &memory, &field);
    let held = CResourceFact::own_designated_allocation(wrap(read), 4);
    let required = CResourceFact::own_designated_allocation(wrap(value), 4);
    assert!(
        resource_fact_entails(&held, &required, &facts),
        "the common matcher knows the producer definition"
    );
    let resources = ResourceContext::new().unchecked_with_fact(held.clone());
    resources.synchronize_memory_equalities(&facts);
    assert_eq!(
        resources.directly_supporting_fact(&required, &facts),
        Some(&held)
    );
}

#[test]
fn class_candidates_follow_merges_and_removals_without_leaking_to_siblings() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(976_100));
    let alias = Pointer::symbolic(Variable(976_101));
    let held = CResourceFact::own_allocation(base.clone(), 4);
    let required = CResourceFact::own_allocation(alias.clone(), 4);
    let facts = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(held.clone());
    resources.synchronize_memory_equalities(&facts);
    let extended = facts.clone().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(
            CPointerValue::new(base, CType::Int32Pointer),
            CPointerValue::new(alias, CType::Int32Pointer),
        ),
        true,
    ));
    assert_eq!(
        resources.directly_supporting_fact(&required, &extended),
        Some(&held)
    );
    assert_eq!(resources.directly_supporting_fact(&required, &facts), None);
    let removed = resources
        .clone()
        .without_exact_representation(&held)
        .unwrap();
    assert_eq!(removed.directly_supporting_fact(&required, &extended), None);
    assert_eq!(
        resources.directly_supporting_fact(&required, &extended),
        Some(&held)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!(
        "../../../scaling_tests/kernel/primitives/resource_algebra/read_definition_index_tests.rs"
    );
}

#[test]
fn definitions_registered_after_publication_select_existing_payloads() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let field = Pointer {
        block: "local:late_field".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = Pointer::symbolic(Variable(976_200));
    let read = Pointer::loaded_value(&memory, &field);
    let wrap = |p| CPointerValue::from_read(p, CType::Int32Pointer, &memory, &field);
    let held = CResourceFact::own_designated_allocation(wrap(read), 4);
    let required = CResourceFact::own_designated_allocation(wrap(value.clone()), 4);
    let facts = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(held.clone());
    resources.synchronize_memory_equalities(&facts);
    assert!(
        resources
            .directly_supporting_fact(&required, &facts)
            .is_none()
    );
    facts
        .equality_graph
        .register_pointer_read_definition(&value, &memory, &field);
    assert_eq!(
        resources.directly_supporting_fact(&required, &facts),
        Some(&held)
    );
}
