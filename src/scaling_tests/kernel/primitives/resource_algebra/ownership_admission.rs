use super::*;

#[test]
fn unsupported_admission_never_discovers_related_owners_or_aliases() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64, 256] {
            let pointer = |id| Pointer::symbolic(Variable(8_780_000 + u64::from(id)));
            let mut facts = PureFactContext::new();
            let mut resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer(0),
                    0u32.into(),
                    4u32.into(),
                    1,
                )),
            );
            for index in 1..count {
                if aliases {
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(pointer(0), pointer(index)),
                        true,
                    );
                } else {
                    resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            pointer(0),
                            (index * 16).into(),
                            (index * 16 + 4).into(),
                            1,
                        ),
                    ));
                }
            }
            resources.synchronize_memory_equalities(&facts);
            let output = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer(0),
                2u32.into(),
                MachineTerm::Variable(Variable(8_790_000)),
                1,
            ));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                resources.clone().admit_without_discovery([output], &facts)
            });
            assert!(matches!(result, OwnershipAdmission::Unsupported(_)));
            samples.push(work);
            assert_eq!(
                resources.facts().len(),
                if aliases { 1 } else { count as usize }
            );
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "aliases={aliases}: {samples:?}"
        );
    }
}

#[test]
fn first_ownership_queries_use_produced_indexes_and_direct_symbolic_bounds() {
    for symbolic in [false, true] {
        for bounded in [false, true] {
            let mut samples = Vec::new();
            for count in [4_u32, 16, 64] {
                let _session = crate::kernel::VerificationSession::enter();
                let p = Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Variable(Variable(8_795_000)),
                };
                let endpoint = MachineTerm::Variable(Variable(8_795_001));
                let mut facts = PureFactContext::new();
                if bounded {
                    facts = facts
                        .assume_condition(
                            ConditionTerm::signed_less_equal(1u32.into(), endpoint.clone()),
                            true,
                        )
                        .assume_condition(
                            ConditionTerm::signed_less_equal(endpoint.clone(), 4u32.into()),
                            true,
                        );
                }
                let mut parent = ResourceContext::new();
                for index in 0..count {
                    parent = parent.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new_with_element_width(
                            p.clone(),
                            (index * 8 + 16).into(),
                            (index * 8 + 20).into(),
                            1,
                        ),
                    ));
                    // More direct bounds on the same selected term must not
                    // become a query-time traversal of its incident facts.
                    if bounded {
                        facts = facts.assume_condition(
                            ConditionTerm::signed_less_equal(
                                endpoint.clone(),
                                (index + 100).into(),
                            ),
                            true,
                        );
                    }
                }
                let query = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    p,
                    0u32.into(),
                    if symbolic { endpoint } else { 4u32.into() },
                    1,
                ));
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let _fast = crate::kernel::search::FastOperationScope::enter(
                        "cold bounded ownership admission",
                    );
                    let result = parent.clone().admit_without_discovery([query], &facts);
                    assert_eq!(
                        matches!(result, OwnershipAdmission::Admitted { .. }),
                        !symbolic || bounded
                    );
                });
                samples.push(work);
            }
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 64),
                "symbolic={symbolic}, bounded={bounded}: {samples:?}"
            );
        }
    }
}

#[test]
fn symbolic_endpoint_refusal_does_not_follow_a_growing_order_chain() {
    let mut samples = Vec::new();
    for count in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |index| MachineTerm::Variable(Variable(8_919_000 + index));
        let mut facts = PureFactContext::new();
        for index in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::signed_less_equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let held = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            Pointer::symbolic(Variable(8_919_100)),
            0u32.into(),
            variable(0),
            1,
        ));
        let query = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            Pointer::symbolic(Variable(8_919_100)),
            variable(count),
            100u32.into(),
            1,
        ));
        let context = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast =
                crate::kernel::search::FastOperationScope::enter("bounded endpoint chain refusal");
            assert!(matches!(
                context.clone().admit_without_discovery([query], &facts),
                OwnershipAdmission::Unsupported(_)
            ));
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn cold_automatic_return_boundaries_do_not_visit_other_allocations() {
    for overlap in [false, true] {
        let mut samples = Vec::new();
        for count in [4u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let local = |index| Pointer {
                block: PointerBlock::Concrete(format!("local:bounded_return_{index}")),
                offset: PointerOffsetTerm::Constant(0),
            };
            let owner = |base, start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base,
                    start.into(),
                    end.into(),
                    1,
                ))
            };
            let mut facts = PureFactContext::new();
            for index in 0..count {
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        local(0),
                        Pointer::symbolic(Variable(8_920_000 + u64::from(index))),
                    ),
                    true,
                );
            }
            let mut frame = ResourceContext::new();
            for index in 0..count {
                frame = frame.unchecked_with_fact(owner(local(index), 0, 4));
            }
            let output = owner(local(if overlap { 0 } else { count }), 0, 4);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast =
                    crate::kernel::search::FastOperationScope::enter("cold automatic return delta");
                let result = frame.admit_returned_frontier(&[output], &facts);
                assert_eq!(
                    matches!(result, FlatBodyAdmission::Conflict { .. }),
                    overlap
                );
                if !overlap {
                    assert!(matches!(result, FlatBodyAdmission::Admitted));
                }
            });
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "overlap={overlap}: {samples:?}"
        );
    }
}
