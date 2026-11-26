use super::*;

#[test]
fn viewability_preservation_checks_only_the_selected_transition_and_facts() {
    for entry_present in [false, true] {
        let costs = [4, 16, 64, 256].map(|size| {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = OldAddress::symbolic(Variable(8_530_000));
            let range = MemoryRange::new_wide(
                pointer.clone(),
                OldMachineTerm::uint64_constant(0),
                OldMachineTerm::Variable(Variable(8_530_001)),
                1,
            );
            let mut memory = SymbolicMemory::new();
            let mut ambient = Vec::new();
            for i in 0..size {
                // Grow the same range's history and unrelated facts together.
                ambient.push(range.loadable_fact(&memory));
                let other = OldAddress::symbolic(Variable(8_531_000 + i));
                ambient
                    .push(MemoryRange::new(other, 0u32.into(), 1u32.into()).loadable_fact(&memory));
                memory = memory.store(pointer.clone(), crate::kernel::int32(i as u32));
            }
            let before = ExecutionState::new().with_memory(memory);
            let declaration = crate::kernel::program_declare("result", ProgramType::Int32);
            let paths = crate::kernel::eval::execute_execution_statement_paths(
                &before,
                &declaration,
                &PureFactContext::new(),
                ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
                &mut ExecutionBudget::default(),
            )
            .unwrap();
            let StatementOutcome::Normal(after) = &paths[0].outcome else {
                panic!("expected a local declaration");
            };
            let footprint = crate::kernel::RegionFootprint::statement_transition(
                "declaration".into(),
                &declaration,
                &before,
                after,
                &paths[0].facts,
            );
            let separation = Proposition::ResourceSeparate {
                left: Box::new(Resource::Footprint(footprint)),
                right: Box::new(Resource::Memory(range.clone())),
            };
            let goal = range.loadable_fact(after.memory());
            ambient.push(separation.clone());
            if entry_present {
                ambient.push(range.loadable_fact(before.memory()));
            }
            let facts = crate::kernel::proof::PureFactStore::from_ordered(&ambient);
            let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
                apply(&separation, None, &goal, None, |p| facts.contains(p))
            });
            if entry_present {
                result.unwrap();
            } else {
                assert_eq!(
                    result.unwrap_err(),
                    "preserve requires viewability at the footprint entry"
                );
            }
            assert!(cost > 0);
            cost
        });
        assert_eq!(costs, [costs[0]; 4], "entry_present={entry_present}");
    }
}

#[test]
fn preservation_does_not_walk_prior_memory_history() {
    for cached in [false, true] {
        let costs = [4, 16, 64, 256].map(|history| {
            let _session = crate::kernel::VerificationSession::enter();
            let _reads = typed_reads::ReadScope::enter();
            let (preservation, goal) = tests::fixture(history, cached);
            let (result, cost) =
                crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
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
fn preservation_work_is_linear_in_explicit_steps() {
    let costs = [1u64, 4, 16, 64].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (preservation, goal) = tests::fixture(4, false);
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..length {
                assert_eq!(preservation.apply(|_| true).unwrap(), goal);
            }
        });
        (length, cost)
    });
    assert!(costs[0].1 > 0);
    assert!(costs.windows(2).all(|p| p[1].1 == p[0].1 * 4), "{costs:?}");
}

#[test]
fn preservation_scalar_names_do_not_walk_prior_memory_history() {
    for value_type in [ProgramType::Int32, ProgramType::UInt8] {
        let costs = [4, 16, 64, 256].map(|history| {
            let _session = crate::kernel::VerificationSession::enter();
            let _reads = typed_reads::ReadScope::enter();
            let (mut preservation, _) = tests::fixture(history, false);
            let (before, after) = preservation.points();
            let (before, after) = (before.clone(), after.clone());
            let proposition = &mut preservation.separation;
            let Proposition::ResourceSeparate { right, .. } = proposition else {
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
            // A byte read is compared through its `int32` widening, as C
            // promotes it.
            let read = |point: &ProgramPoint| {
                let bits = integer_bits(tests::observe_point(point, &address, value_type)).unwrap();
                Box::new(if value_type == ProgramType::UInt8 {
                    OldMachineTerm::machine_integer_cast(
                        MachineIntegerType::UInt8,
                        MachineIntegerType::Int32,
                        bits,
                    )
                } else {
                    bits
                })
            };
            let goal = Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: read(&after),
                    right: read(&before),
                },
                true,
            );
            preservation.result = goal.clone();
            let (result, cost) =
                crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
            assert_eq!(result.unwrap(), goal);
            if value_type == ProgramType::UInt8 {
                // A one-byte separation must not preserve a four-byte read,
                // even when both read types are present at the same address.
                let wider = Proposition::condition_is(
                    OldConditionTerm::equal(
                        integer_bits(tests::observe_point(&after, &address, ProgramType::Int32))
                            .unwrap(),
                        integer_bits(tests::observe_point(&before, &address, ProgramType::Int32))
                            .unwrap(),
                    ),
                    true,
                );
                preservation.result = wider;
                assert!(preservation.apply(|_| true).is_err());
            }
            cost
        });
        assert!(costs[0] > 0);
        assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
    }
}

#[test]
fn preservation_uses_selected_observations_without_scanning_the_registry() {
    let costs = [4, 16, 64, 256].map(|unrelated| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (preservation, goal) = tests::fixture(2, false);
        let memory = SymbolicMemory::new();
        for index in 0..unrelated {
            tests::observe(
                &memory,
                &OldAddress::symbolic(Variable(8_410_000 + index)),
                ProgramType::Int32Pointer,
            );
        }
        let (result, cost) =
            crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
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
        let (before, after) = original.points();
        let entry = ExecutionState::at_point(before);
        let exit = ExecutionState::at_point(after);
        let effects = Vec::<ExecutionPureFact>::new();
        let (footprint, recording_cost) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::RegionFootprint::transition(
                    "statement(0).footprint".into(),
                    &entry,
                    &exit,
                    &effects,
                )
            });
        let Proposition::ResourceSeparate { right, .. } = &original.separation else {
            unreachable!()
        };
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: right.clone(),
        };
        let preservation = tests::Preservation {
            separation,
            field: None,
            result: goal.clone(),
        };
        let (result, application_cost) =
            crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
        assert_eq!(result.unwrap(), goal);
        (recording_cost, application_cost)
    });
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn shared_branch_write_footprint_uses_only_its_arm_endpoints() {
    let costs = [4, 16, 64, 256].map(|history| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = SymbolicMemory::new();
        for index in 0..history {
            memory = memory.store(
                OldAddress::symbolic(Variable(8_541_000 + index)),
                crate::kernel::int32(0),
            );
        }
        let entry = ExecutionState::new().with_memory(memory);
        let target = OldAddress::symbolic(Variable(8_540_000));
        let arm = |address: &OldAddress, value| {
            let exit = entry.clone().with_memory(
                entry
                    .memory()
                    .clone()
                    .store(address.clone(), crate::kernel::int32(value)),
            );
            let effects = vec![ExecutionPureFact::certified(
                Proposition::MemoryMutatesOnly {
                    before: entry.memory().clone(),
                    after: exit.memory().clone(),
                    writes: vec![(address.clone(), crate::kernel::AccessExtent::from(4))],
                },
            )];
            let footprint = crate::kernel::RegionFootprint::transition(
                "arm write".into(),
                &entry,
                &exit,
                &effects,
            );
            (exit, footprint)
        };
        let (left, left_effect) = arm(&target, 1);
        let (right, right_effect) = arm(&target, 2);
        let (other, other_effect) = arm(&OldAddress::symbolic(Variable(8_540_001)), 2);
        let (joined, cost) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::RegionFootprint::shared_branch_write(
                "branch".into(),
                &entry,
                &left,
                [(&left, Some(&left_effect)), (&right, Some(&right_effect))],
            )
        });
        assert_eq!(joined.unwrap().members, left_effect.members);
        assert!(
            crate::kernel::RegionFootprint::shared_branch_write(
                "branch".into(),
                &entry,
                &left,
                [(&left, Some(&left_effect)), (&other, Some(&other_effect))],
            )
            .is_none()
        );
        cost
    });
    assert_eq!(costs, [costs[0]; 4]);
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
            OldAddress::symbolic(Variable(8_390_100)),
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
                OldAddress {
                    base: AddressBase::ExternalArgument,
                    offset: OldAddressOffset::Variable(Variable(8_391_000 + index)),
                },
                0u32.into(),
                4u32.into(),
                1,
            )
        };
        let kept = Resource::Memory(range(1000));
        let ranges = (0..count).map(range).collect::<Vec<_>>();
        let facts = ranges.iter().fold(PureFactContext::new(), |facts, range| {
            facts.assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(range.clone())),
                right: Box::new(kept.clone()),
            })
        });
        let effects = vec![ExecutionPureFact::certified(
            Proposition::MemoryEffectSummary {
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
            Proposition::MemoryEffectSummary {
                before: state.memory().clone(),
                after: state.memory().clone(),
                mutable_ranges: (0..count)
                    .map(|index| {
                        MemoryRange::new_with_element_width(
                            OldAddress::symbolic(Variable(8_392_000 + index)),
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
        let (preservation, goal) = tests::resource_fixture(size);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
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
        let (preservation, goal) = tests::resource_history_fixture(history);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
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
        let (preservation, goal) = tests::abstract_fixture(history);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| preservation.apply(|_| true));
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
        let (preservation, separation, old, goal) =
            tests::definedness_fixture(size, ProgramType::UInt8);
        let mut facts = crate::kernel::proof::PureFactStore::from_ordered(&[]);
        facts = facts.with_fact(separation);
        facts = facts.with_fact(old.clone());
        for i in 0..size {
            let Proposition::MemoryReadDefined {
                memory,
                pointer,
                value_type,
                ..
            } = &old
            else {
                unreachable!()
            };
            facts = facts.with_fact(Proposition::MemoryReadDefined {
                at: None,
                memory: memory
                    .clone()
                    .store(pointer.clone(), ProgramValue::Int32((i as u32).into())),
                pointer: pointer.clone(),
                value_type: *value_type,
            });
            facts = facts.with_fact(Proposition::MemoryReadDefined {
                at: None,
                memory: memory.clone(),
                pointer: OldAddress::symbolic(Variable(8_500_000 + i)),
                value_type: *value_type,
            });
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            preservation.apply(|p| facts.contains(p))
        });
        assert_eq!(result.unwrap(), goal);
        work
    });
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
    assert!(costs[0] > 0);
}

#[test]
fn preservation_separation_orientations_use_exact_indexes() {
    for reversed in [false, true] {
        for present in [false, true] {
            let costs = [1, 4, 16].map(|size| {
                let _session = crate::kernel::VerificationSession::enter();
                let _reads = typed_reads::ReadScope::enter();
                let (preservation, goal) = tests::fixture(4, false);
                let Proposition::ResourceSeparate { left, right } = &preservation.separation else {
                    unreachable!()
                };
                let mut ambient = Vec::new();
                for index in 0..size {
                    let other = Resource::Memory(MemoryRange::new_with_element_width(
                        OldAddress::symbolic(Variable(8_900_000 + index)),
                        0u32.into(),
                        1u32.into(),
                        4,
                    ));
                    // Grow both separations of this same footprint and
                    // unrelated separations. Neither may be scanned on a miss.
                    ambient.push(Proposition::ResourceSeparate {
                        left: left.clone(),
                        right: Box::new(other.clone()),
                    });
                    ambient.push(Proposition::ResourceSeparate {
                        left: Box::new(other),
                        right: right.clone(),
                    });
                }
                if present {
                    ambient.push(if reversed {
                        Proposition::ResourceSeparate {
                            left: right.clone(),
                            right: left.clone(),
                        }
                    } else {
                        preservation.separation.clone()
                    });
                }
                let facts = crate::kernel::proof::facts::PureFactStore::from_ordered(&ambient);
                let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
                    preservation.apply(|fact| facts.contains(fact))
                });
                if present {
                    assert_eq!(result.unwrap(), goal);
                } else {
                    assert_eq!(
                        result.unwrap_err(),
                        "preserve separation is not exactly available"
                    );
                }
                assert!(cost > 0);
                cost
            });
            assert!(
                costs.iter().all(|cost| *cost == costs[0]),
                "reversed={reversed}, present={present}: {costs:?}"
            );
        }
    }
}

#[test]
fn wide_resource_field_preservation_scales_with_explicit_steps_not_ambient_instances() {
    for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
        let mut baseline = None;
        for instances in [4, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let value = OldMachineTerm::Variable(Variable(8_390_901));
            let (preservation, goal) =
                tests::resource_fixture_with_values(instances, format, value.clone(), value);
            for steps in [1, 4, 16, 64] {
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..steps {
                        assert_eq!(
                            preservation
                                .apply(|p| p == &preservation.separation)
                                .unwrap(),
                            goal
                        );
                    }
                });
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                let one = *baseline.get_or_insert(work);
                assert_eq!(
                    work,
                    one * steps,
                    "{format:?}: {instances} instances, {steps} steps"
                );
            }
        }
    }
}
