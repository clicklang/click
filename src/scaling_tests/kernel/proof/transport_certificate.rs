use super::*;

#[test]
fn transport_certificate_does_not_walk_prior_memory_history() {
    for cached in [false, true] {
        let costs = [4, 16, 64, 256].map(|history| {
            let _session = crate::kernel::VerificationSession::enter();
            let _reads = typed_reads::ReadScope::enter();
            let (certificate, goal) = tests::fixture(history, cached);
            let (result, cost) =
                crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
            assert_eq!(result.unwrap(), goal);
            assert!(cost > 0);
            cost
        });
        assert!(
            costs.iter().all(|cost| *cost == costs[0]),
            "cached={cached}: {costs:?}"
        );
    }
}

#[test]
fn transport_certificate_work_is_linear_in_explicit_nodes() {
    let costs = [1u64, 4, 16, 64].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let equality = |left: u64, right: u64| {
            Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(
                    Box::new(PointerValue::new(
                        Pointer::symbolic(Variable(8_390_000 + left)),
                        ProgramType::Int32Pointer,
                    )),
                    Box::new(PointerValue::new(
                        Pointer::symbolic(Variable(8_390_000 + right)),
                        ProgramType::Int32Pointer,
                    )),
                ),
                true,
            )
        };
        let mut certificate = TransportCertificate {
            nodes: vec![TransportNode::Premise {
                proposition: equality(0, 1),
                result: equality(0, 1),
            }],
            conclusion: 0,
        };
        let mut previous = 0;
        for i in 1..length {
            let next = certificate.nodes.len();
            certificate.nodes.push(TransportNode::Premise {
                proposition: equality(i, i + 1),
                result: equality(i, i + 1),
            });
            certificate.nodes.push(TransportNode::Transitive {
                left: previous,
                right: next,
                result: equality(0, i + 1),
            });
            previous = next + 1;
        }
        let goal = equality(0, length);
        certificate.conclusion = previous;
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        (length, cost)
    });
    assert!(costs.windows(2).all(|p| p[1].1 <= p[0].1 * 8), "{costs:?}");
}

#[test]
fn transport_certificate_scalar_names_do_not_walk_prior_memory_history() {
    for value_type in [ProgramType::Int32, ProgramType::UInt8] {
        let costs = [4, 16, 64, 256].map(|history| {
            let _session = crate::kernel::VerificationSession::enter();
            let _reads = typed_reads::ReadScope::enter();
            let (mut certificate, _) = tests::fixture(history, false);
            let TransportNode::Premise {
                proposition: Proposition::CMemoryMutatesOnly { before, after, .. },
                ..
            } = &certificate.nodes[0]
            else {
                unreachable!()
            };
            let before = intern_c_memory(before.clone());
            let after = intern_c_memory(after.clone());
            let TransportNode::Premise {
                proposition,
                result,
            } = &mut certificate.nodes[1]
            else {
                unreachable!()
            };
            let Proposition::CResourceSeparate { right, .. } = proposition else {
                unreachable!()
            };
            let Resource::Memory(range) = right.as_ref() else {
                unreachable!()
            };
            let (address, _) = range.byte_footprint();
            **right = Resource::Memory(MemoryRange::new_with_element_width(
                address.clone(),
                0u32.into(),
                1u32.into(),
                value_type.byte_width(),
            ));
            *result = proposition.clone();
            // A byte read is compared through its `int32` widening, as C
            // promotes it.
            let read = |memory: &SharedMemory| {
                let bits =
                    integer_bits(tests::observe(memory.memory(), &address, value_type)).unwrap();
                Box::new(if value_type == ProgramType::UInt8 {
                    MachineTerm::machine_integer_cast(
                        MachineIntegerType::UInt8,
                        MachineIntegerType::Int32,
                        bits,
                    )
                } else {
                    bits
                })
            };
            let goal = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: read(&after),
                    right: read(&before),
                },
                true,
            );
            certificate.nodes[2] = TransportNode::Preserve {
                field: None,
                effect: Some(0),
                separation: 1,
                result: goal.clone(),
            };
            let (result, cost) =
                crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
            assert_eq!(result.unwrap(), goal);
            if value_type == ProgramType::UInt8 {
                // A one-byte separation must not preserve a four-byte read,
                // even when both read types are present at the same address.
                let wider = Proposition::ConditionIs(
                    ConditionTerm::equal(
                        integer_bits(tests::observe(after.memory(), &address, ProgramType::Int32))
                            .unwrap(),
                        integer_bits(tests::observe(
                            before.memory(),
                            &address,
                            ProgramType::Int32,
                        ))
                        .unwrap(),
                    ),
                    true,
                );
                certificate.nodes[2] = TransportNode::Preserve {
                    field: None,
                    effect: Some(0),
                    separation: 1,
                    result: wider,
                };
                assert!(certificate.apply(|_| true).is_err());
            }
            cost
        });
        assert!(costs[0] > 0);
        assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
    }
}

#[test]
fn transport_certificate_uses_selected_observations_without_scanning_the_registry() {
    let costs = [4, 16, 64, 256].map(|unrelated| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (certificate, goal) = tests::fixture(2, false);
        let memory = Memory::new();
        for index in 0..unrelated {
            tests::observe(
                &memory,
                &Pointer::symbolic(Variable(8_410_000 + index)),
                ProgramType::Int32Pointer,
            );
        }
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        cost
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn region_footprint_preservation_does_not_walk_prior_memory_history() {
    let costs = [4, 16, 64, 256].map(|history| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (original, goal) = tests::fixture(history, false);
        let TransportNode::Premise {
            proposition: effect,
            ..
        } = &original.nodes[0]
        else {
            unreachable!()
        };
        let Proposition::CMemoryMutatesOnly { before, after, .. } = effect else {
            unreachable!()
        };
        let entry = ExecutionState::new().with_memory(before.clone());
        let exit = entry.clone().with_memory(after.clone());
        let effects = vec![ExecutionPureFact::certified(effect.clone())];
        let (footprint, recording_cost) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::RegionFootprint::transition(
                    "statement(0).footprint".into(),
                    &entry,
                    &exit,
                    &effects,
                )
            });
        let TransportNode::Premise {
            proposition: Proposition::CResourceSeparate { right, .. },
            ..
        } = &original.nodes[1]
        else {
            unreachable!()
        };
        let separation = Proposition::CResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: right.clone(),
        };
        let certificate = TransportCertificate {
            nodes: vec![
                TransportNode::Premise {
                    proposition: separation.clone(),
                    result: separation,
                },
                TransportNode::Preserve {
                    field: None,
                    effect: None,
                    separation: 0,
                    result: goal.clone(),
                },
            ],
            conclusion: 1,
        };
        let (result, application_cost) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        (recording_cost, application_cost)
    });
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn simple_footprint_separation_does_not_walk_a_region_sequence() {
    let costs = [4, 16, 64, 256].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new();
        let leaf = crate::kernel::RegionFootprint::transition(
            "statement(0).footprint".into(),
            &state,
            &state,
            &crate::kernel::ExecutionFacts::new(),
        );
        let members = (0..length)
            .map(|_| Resource::Footprint(leaf.clone()))
            .collect();
        let region = Resource::Footprint(crate::kernel::RegionFootprint::sequence(
            "function.footprint".into(),
            &state,
            &state,
            members,
            true,
        ));
        let kept = Resource::Memory(MemoryRange::new_with_element_width(
            Pointer::symbolic(Variable(8_390_100)),
            0u32.into(),
            1u32.into(),
            4,
        ));
        let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::region_footprint::separate_using(&region, &kept, &PureFactContext::new())
        });
        assert!(
            !result,
            "a multi-transition region needs explicit composition"
        );
        cost
    });
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn selected_footprint_separations_are_linear_with_one_shared_address_bucket() {
    let costs = [4u64, 16, 64, 256].map(|count| {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new();
        let range = |index: u64| {
            MemoryRange::new_with_element_width(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Variable(Variable(8_391_000 + index)),
                },
                0u32.into(),
                4u32.into(),
                1,
            )
        };
        let kept = Resource::Memory(range(1000));
        let ranges = (0..count).map(range).collect::<Vec<_>>();
        let facts = ranges.iter().fold(PureFactContext::new(), |facts, range| {
            facts.assume_proposition(Proposition::CResourceSeparate {
                left: Box::new(Resource::Memory(range.clone())),
                right: Box::new(kept.clone()),
            })
        });
        let effects = vec![ExecutionPureFact::certified(
            Proposition::CMemoryEffectSummary {
                before: state.memory().clone(),
                after: state.memory().clone(),
                mutable_ranges: ranges,
            },
        )];
        let footprint = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "region(0).footprint".into(),
            &state,
            &state,
            &effects,
        ));
        let (separate, cost) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::region_footprint::separate_using(&footprint, &kept, &facts)
        });
        assert!(separate);
        assert!(cost > 0);
        (count, cost)
    });
    for pair in costs.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{costs:?}");
    }
}

#[test]
fn two_footprints_do_not_expand_into_a_cartesian_product() {
    let costs = [4u64, 16, 64, 256].map(|count| {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new();
        let resources = (0..count).fold(state.resources().clone(), |resources, index| {
            resources.unchecked_with_fact(ResourceFact::own_token(
                format!("changed_{index}"),
                Vec::new(),
            ))
        });
        let after = state.clone().with_resource_context(resources);
        let tokens = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "region(0).footprint".into(),
            &state,
            &after,
            &crate::kernel::ExecutionFacts::new(),
        ));
        let effects = vec![ExecutionPureFact::certified(
            Proposition::CMemoryEffectSummary {
                before: state.memory().clone(),
                after: state.memory().clone(),
                mutable_ranges: (0..count)
                    .map(|index| {
                        MemoryRange::new_with_element_width(
                            Pointer::symbolic(Variable(8_392_000 + index)),
                            0u32.into(),
                            4u32.into(),
                            1,
                        )
                    })
                    .collect(),
            },
        )];
        let memory = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "region(1).footprint".into(),
            &state,
            &state,
            &effects,
        ));
        let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::region_footprint::separate_using(
                &tokens,
                &memory,
                &PureFactContext::new(),
            )
        });
        assert!(
            !result,
            "a simple step must not compare every pair of effects"
        );
        cost
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

#[test]
fn selected_resource_field_preservation_does_not_scan_ambient_instances() {
    let costs = [4, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (certificate, goal) = tests::resource_fixture(size);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        work
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

#[test]
fn selected_resource_field_preservation_does_not_walk_instance_history() {
    let costs = [4, 16, 64, 256].map(|history| {
        let _session = crate::kernel::VerificationSession::enter();
        let (certificate, goal) = tests::resource_history_fixture(history);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        work
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

#[test]
fn abstract_memory_preservation_does_not_walk_read_history() {
    let costs = [4, 16, 64, 256].map(|history| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (certificate, goal) = tests::abstract_fixture(history);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| certificate.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        work
    });
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|work| *work == costs[0]), "{costs:?}");
}

#[test]
fn definedness_preservation_ignores_history_and_ambient_facts() {
    let costs = [4, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (certificate, separation, old, goal) =
            tests::definedness_fixture(size, ProgramType::UInt8);
        let mut facts = crate::kernel::proof::ProofFacts::from_ordered(&[]);
        facts = facts.with_fact(separation);
        facts = facts.with_fact(old.clone());
        for i in 0..size {
            let Proposition::CMemoryReadDefined {
                memory,
                pointer,
                value_type,
            } = &old
            else {
                unreachable!()
            };
            facts = facts.with_fact(Proposition::CMemoryReadDefined {
                memory: memory
                    .clone()
                    .store(pointer.clone(), ProgramValue::Int32((i as u32).into())),
                pointer: pointer.clone(),
                value_type: *value_type,
            });
            facts = facts.with_fact(Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: Pointer::symbolic(Variable(8_500_000 + i)),
                value_type: *value_type,
            });
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.apply(|p| facts.contains(p))
        });
        assert_eq!(result.unwrap(), goal);
        work
    });
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
    assert!(costs[0] > 0);
}
