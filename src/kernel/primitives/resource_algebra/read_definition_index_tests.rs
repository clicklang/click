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

#[test]
fn memory_direct_support_preserves_held_identity_and_authority() {
    for native in [false, true] {
        for owned in [false, true] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = PureFactContext::new();
            let p = Pointer::symbolic(Variable(976_300));
            let range = |start: u32, end: u32| {
                if native {
                    CMemoryRange::new_wide(
                        p.clone(),
                        MachineTerm::uint64_constant(start.into()),
                        MachineTerm::uint64_constant(end.into()),
                        4,
                    )
                } else {
                    CMemoryRange::new(p.clone(), start.into(), end.into())
                }
            };
            let held = if owned {
                CResourceFact::own_memory(range(0, 4))
            } else {
                CResourceFact::view_memory(range(0, 4))
            };
            let context =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held.clone());
            context.synchronize_memory_equalities(&facts);
            let required = CResourceFact::view_memory(range(1, 3).with_typed_carrier());
            for _ in 0..3 {
                assert!(context.satisfies_fact(&required, &facts));
                assert_eq!(
                    context.directly_supporting_fact(&required, &facts),
                    Some(&held)
                );
                assert_eq!(
                    context
                        .directly_supporting_fact(&CResourceFact::own_memory(range(1, 3)), &facts)
                        .is_some(),
                    owned
                );
                assert!(
                    context
                        .directly_supporting_fact(&CResourceFact::view_memory(range(0, 8)), &facts)
                        .is_none()
                );
                let wrong = CResourceFact::view_memory(
                    range(1, 3)
                        .with_designation(std::sync::Arc::new(Pointer::symbolic(Variable(976_301))))
                        .with_typed_carrier(),
                );
                assert!(context.directly_supporting_fact(&wrong, &facts).is_none());
                assert!(!context.satisfies_fact(&wrong, &facts));
                assert!(context.contains_exact_representation(&held));
            }
            let child = context.clone().without_exact_representation(&held).unwrap();
            assert!(child.directly_supporting_fact(&required, &facts).is_none());
            assert!(!child.satisfies_fact(&required, &facts));
            assert_eq!(
                context.directly_supporting_fact(&required, &facts),
                Some(&held)
            );
            for quantity in [0u32, u32::MAX] {
                let invalid = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
                    CResourceFact::own_quantity(CResource::Memory(range(0, 4)), quantity.into()),
                );
                assert!(!invalid.satisfies_fact(&required, &facts));
                assert!(
                    invalid
                        .directly_supporting_fact(&CResourceFact::own_memory(range(1, 3)), &facts)
                        .is_none()
                );
            }
        }
    }
}
