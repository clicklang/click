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
                // Neither endpoint supplies a separation certificate.
                MachineTerm::Variable(Variable(8_790_001)),
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
fn certified_group_and_loop_exchange_keep_fixed_memory_boundaries_as_aliases_grow() {
    for aliases in [false, true] {
        let mut group_samples = Vec::new();
        let mut loop_samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(8_797_000));
            let owner = |start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base.clone(),
                    start.into(),
                    end.into(),
                    1,
                ))
            };
            let mut assumptions = PureFactContext::new();
            let before = owner(0, 4);
            let body = ResourceContext::new().unchecked_with_fact(before.clone());
            let mut frame = body.clone();
            for index in 0..count {
                if aliases {
                    assumptions = assumptions.assume_condition(
                        ConditionTerm::pointer_equal(
                            base.clone(),
                            Pointer::symbolic(Variable(8_798_000 + u64::from(index))),
                        ),
                        true,
                    );
                } else {
                    frame = frame.unchecked_with_fact(owner(32 + 8 * index, 36 + 8 * index));
                }
            }
            frame.synchronize_memory_equalities(&assumptions);
            let exit = body
                .clone()
                .without_exact_representation(&before)
                .unwrap()
                .unchecked_with_facts([owner(0, 2), owner(2, 4)]);
            let sources = [owner(0, 2), owner(2, 4)]
                .map(|fact| exit.unique_owned_occurrence_for_fact(&fact).unwrap().0);
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                exit.restore_frame_after_exchange(&body, &frame, &assumptions)
                    .unwrap()
            });
            for (fact, source) in [owner(0, 2), owner(2, 4)].into_iter().zip(sources) {
                assert_eq!(restored.owned_fact_for_occurrence(source), Some(&fact));
            }
            loop_samples.push(work);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let added = frame
                    .clone()
                    .try_compose_certified_group_into_valid_context_delaying_normalization(
                        [owner(4, 6), owner(6, 8)],
                        &assumptions,
                    )
                    .unwrap();
                assert!(added.contains_exact_representation(&owner(4, 6)));
                let outputs = ResourceContext::new_with_equalities(&assumptions)
                    .unchecked_with_facts([owner(4, 6), owner(6, 8)]);
                let joined = frame
                    .clone()
                    .compose_checked_outputs(&outputs, &assumptions)
                    .unwrap();
                assert!(joined.contains_exact_representation(&owner(6, 8)));
                assert!(
                    frame
                        .clone()
                        .try_compose_certified_group_into_valid_context_delaying_normalization(
                            [owner(3, 5)],
                            &assumptions
                        )
                        .is_err()
                );
            });
            group_samples.push(work);
        }
        eprintln!(
            "certified boundary aliases={aliases}: {group_samples:?}; loop exchange: {loop_samples:?}"
        );
        for samples in [group_samples, loop_samples] {
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 32),
                "{aliases}: {samples:?}"
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
