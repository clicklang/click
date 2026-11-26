use super::*;

#[test]
fn unsupported_admission_never_discovers_related_owners_or_aliases() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64, 256] {
            let pointer = |id| OldAddress::symbolic(Variable(8_780_000 + u64::from(id)));
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
                        OldConditionTerm::address_equal(pointer(0), pointer(index)),
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
                1u32.into(),
                OldMachineTerm::Variable(Variable(8_790_000)),
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
                let p = OldAddress {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::variable(Variable(8_795_000)),
                };
                let endpoint = OldMachineTerm::Variable(Variable(8_795_001));
                let mut facts = PureFactContext::new();
                if bounded {
                    facts = facts
                        .assume_condition(
                            OldConditionTerm::signed_less_equal(1u32.into(), endpoint.clone()),
                            true,
                        )
                        .assume_condition(
                            OldConditionTerm::signed_less_equal(endpoint.clone(), 4u32.into()),
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
                            OldConditionTerm::signed_less_equal(
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
            let base = OldAddress::symbolic(Variable(8_797_000));
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
                        OldConditionTerm::address_equal(
                            base.clone(),
                            OldAddress::symbolic(Variable(8_798_000 + u64::from(index))),
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
fn symbolic_boundaries_are_bounded_as_owners_aliases_and_explicit_frames_grow() {
    for axis in [
        "owners",
        "aliases",
        "same-block aliases",
        "explicit frame",
        "views after removal",
    ] {
        let mut samples = Vec::new();
        for count in [4_u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = if axis == "views after removal" {
                OldAddress {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::variable(Variable(8_798_100)),
                }
            } else {
                OldAddress::symbolic(Variable(8_798_100))
            };
            let n = OldMachineTerm::Variable(Variable(8_798_101));
            let m = OldMachineTerm::Variable(Variable(8_798_102));
            let span = |start, end| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base.clone(),
                    start,
                    end,
                    1,
                ))
            };
            let mut facts = PureFactContext::new()
                .assume_condition(
                    OldConditionTerm::signed_less_equal(1u32.into(), n.clone()),
                    true,
                )
                .assume_condition(
                    OldConditionTerm::signed_less_equal(n.clone(), 8u32.into()),
                    true,
                );
            let held = span(0u32.into(), n.clone());
            let output = span(
                n.clone(),
                if axis == "explicit frame" {
                    m.clone()
                } else {
                    16u32.into()
                },
            );
            let mut owners = vec![held];
            if axis == "explicit frame" {
                owners.push(span(m, 24u32.into()));
            }
            for index in 0..count {
                match axis {
                    "aliases" | "same-block aliases" => {
                        let other = if axis == "aliases" {
                            OldAddress::symbolic(Variable(8_799_000 + index))
                        } else {
                            OldAddress {
                                base: base.base.clone(),
                                offset: AddressOffset::variable(Variable(8_799_000 + index)),
                            }
                        };
                        facts = facts.assume_condition(
                            OldConditionTerm::address_equal(base.clone(), other),
                            true,
                        );
                    }
                    _ => owners.push(span(
                        (32 + 2 * index as u32).into(),
                        (33 + 2 * index as u32).into(),
                    )),
                }
            }
            let mut frame = ResourceContext::new_with_equalities(&facts);
            if axis == "views after removal" {
                let old = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    OldAddress {
                        base: AddressBase::ExternalArgument,
                        offset: AddressOffset::variable(Variable(8_798_103)),
                    },
                    0u32.into(),
                    1u32.into(),
                    1,
                ));
                frame = frame.unchecked_with_fact(old.clone());
                frame.synchronize_memory_equalities(&facts);
                frame = frame.without_exact_representation(&old).unwrap();
                for view in 0..count {
                    frame = frame.unchecked_with_fact(ResourceFact::view_memory(
                        MemoryRange::new_with_element_width(
                            OldAddress {
                                base: AddressBase::ExternalArgument,
                                offset: AddressOffset::variable(Variable(8_798_200 + view)),
                            },
                            0u32.into(),
                            1u32.into(),
                            1,
                        ),
                    ));
                }
            }
            frame = frame.unchecked_with_facts(owners.clone());
            frame.synchronize_memory_equalities(&facts);
            if axis == "explicit frame" {
                let conjunction = owners.iter().rev().fold(Resource::Emp, |rest, fact| {
                    Resource::star(rest, fact.resource().clone())
                });
                facts = facts.assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(output.resource().clone()),
                    right: Box::new(conjunction),
                });
                // Index maintenance belongs to explicit proof admission. The
                // query below only selects its retained source by exact root.
                frame.synchronize_memory_equalities(&facts);
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast = crate::kernel::search::FastOperationScope::enter(
                    "symbolic ownership boundary scaling",
                );
                frame
                    .clone()
                    .try_compose_checked_ownership_and_occurrences([output.clone()], &facts)
            });
            assert!(result.is_ok(), "{axis}/{count}: {result:?}");
            samples.push(work);
        }
        eprintln!("symbolic boundary {axis}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 48),
            "{axis}: {samples:?}"
        );
    }
}

#[test]
fn symbolic_outputs_against_private_scalar_frames_do_not_visit_the_slots() {
    let mut samples = Vec::new();
    for count in [4_usize, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        crate::kernel::set_never_address_taken_locals(
            (0..count)
                .map(|i| format!("boundary_hidden_{i}").into())
                .collect(),
        );
        let facts = PureFactContext::new();
        let frame = ResourceContext::new().unchecked_with_facts((0..count).map(|i| {
            ResourceFact::own_memory(MemoryRange::new(
                crate::kernel::SymbolicMemory::local_pointer(format!("boundary_hidden_{i}")),
                0u32.into(),
                4u32.into(),
            ))
        }));
        let output = ResourceFact::own_memory(MemoryRange::new(
            OldAddress::symbolic(Variable(8_798_901)),
            0u32.into(),
            OldMachineTerm::Variable(Variable(8_798_902)),
        ));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast =
                crate::kernel::search::FastOperationScope::enter("private frame coverage scaling");
            frame.clone().admit_without_discovery([output], &facts)
        });
        assert!(matches!(result, OwnershipAdmission::Admitted { .. }));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "private frame: {samples:?}"
    );
}

#[test]
fn entry_argument_and_automatic_storage_boundaries_do_not_visit_owner_blocks() {
    for query_is_local in [false, true] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = PureFactContext::new();
            let range = |block, offset| {
                ResourceFact::own_memory(MemoryRange::new(
                    OldAddress {
                        base: block,
                        offset: AddressOffset::constant(offset),
                    },
                    0u32.into(),
                    4u32.into(),
                ))
            };
            let frame = ResourceContext::new().unchecked_with_facts((0..count).map(|i| {
                if query_is_local {
                    range(AddressBase::ExternalArgument, i64::from(i) * 8)
                } else {
                    range(AddressBase::Concrete(format!("local:boundary_{i}")), 0)
                }
            }));
            let output = if query_is_local {
                range(AddressBase::Concrete("local:output".into()), 0)
            } else {
                range(AddressBase::ExternalArgument, 0)
            };
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast = crate::kernel::search::FastOperationScope::enter(
                    "allocation-class boundary scaling",
                );
                frame.checked_frontier_boundary_conflict(&[output], &facts)
            });
            assert!(matches!(result, Ok(None)));
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{query_is_local}: {samples:?}"
        );
    }
}

#[test]
fn selected_unfold_frame_restoration_does_not_visit_unrelated_owners() {
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let instance = ResourceInstance::new(
            InstanceId::from_variable(Variable(8_798_950)),
            "framed_body".into(),
            vec![].into(),
            ResourceFieldSchema::new(vec![(
                "tag".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![ProgramValue::Int32(OldMachineTerm::constant(7)).into()].into(),
        )
        .unwrap();
        let owner = |id| {
            ResourceFact::own_memory(MemoryRange::new(
                OldAddress::symbolic(Variable(id)),
                0u32.into(),
                4u32.into(),
            ))
        };
        let child = owner(8_798_951);
        let body = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone())));
        let frame = body
            .clone()
            .unchecked_with_facts((0..count).map(|i| owner(8_799_000 + i)));
        let exit = body
            .clone()
            .unfold_instance_body(&instance, [child.clone()], &facts)
            .unwrap()
            .unwrap();
        let occurrence = exit.unique_owned_occurrence_for_fact(&child).unwrap().0;
        let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast = crate::kernel::search::FastOperationScope::enter(
                "selected unfold loop-frame restoration",
            );
            exit.restore_frame_after_exchange(&body, &frame, &facts)
                .unwrap()
        });
        assert_eq!(restored.owned_fact_for_occurrence(occurrence), Some(&child));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 48),
        "selected unfold frame: {samples:?}"
    );
}

#[test]
fn symbolic_endpoint_refusal_does_not_follow_a_growing_order_chain() {
    let mut samples = Vec::new();
    for count in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |index| OldMachineTerm::Variable(Variable(8_919_000 + index));
        let mut facts = PureFactContext::new();
        for index in 0..count {
            facts = facts.assume_condition(
                OldConditionTerm::signed_less_equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let held = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            OldAddress::symbolic(Variable(8_919_100)),
            0u32.into(),
            variable(0),
            1,
        ));
        let query = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            OldAddress::symbolic(Variable(8_919_100)),
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
            let local = |index| OldAddress {
                base: AddressBase::Concrete(format!("local:bounded_return_{index}")),
                offset: AddressOffset::constant(0),
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
                    OldConditionTerm::address_equal(
                        local(0),
                        OldAddress::symbolic(Variable(8_920_000 + u64::from(index))),
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

#[test]
fn legacy_composition_cost_tracks_the_delta_and_written_neighbors() {
    for axis in ["owners", "related", "aliases", "same token"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = OldAddress::symbolic(Variable(8_798_100));
            let range = |base, start: u32| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base,
                    start.into(),
                    (start + 4).into(),
                    1,
                ))
            };
            let token = ResourceFact::own(Resource::Token {
                name: "credit".into(),
                arguments: vec![].into(),
            });
            let mut facts = PureFactContext::new();
            let mut frame = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_fact(range(pointer.clone(), 0));
            for index in 1..=count {
                let other = OldAddress::symbolic(Variable(8_798_200 + u64::from(index)));
                match axis {
                    "aliases" => {
                        facts = facts.assume_condition(
                            OldConditionTerm::address_equal(pointer.clone(), other),
                            true,
                        )
                    }
                    "related" => {
                        frame = frame.unchecked_with_fact(range(pointer.clone(), index * 16))
                    }
                    "same token" => {
                        frame =
                            frame.unchecked_with_fact(ResourceFact::View(token.resource().clone()))
                    }
                    _ => frame = frame.unchecked_with_fact(range(other, 0)),
                }
            }
            frame.synchronize_memory_equalities(&facts);
            let addition = if axis == "owners" || axis == "same token" {
                token
            } else {
                range(pointer.clone(), 4)
            };
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast =
                    crate::kernel::search::FastOperationScope::enter("legacy checked delta");
                frame.clone().try_compose_with_fact(addition, &facts)
            });
            result.unwrap();
            samples.push(work);
        }
        assert!(samples[2] <= samples[0] * 3 + 96, "{axis}: {samples:?}");
    }
}
