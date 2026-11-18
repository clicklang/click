// Full-call controls for local-storage classification and escrow restoration.
use super::*;

/// Reuse the selected call reservation beside a growing folded caller frame.
/// A view of cell(p) borrows wide(p), even when unrelated folds were
/// inserted first. Supplier selection must not open their bodies.
#[test]
fn folded_view_preparation_uses_the_indexed_owner() {
    let cell = cell_definition(1, Vec::new());
    let wide = wide_definition(2);
    let decoy = CompositeResourceDefinition::new(
        "decoy",
        vec![program_parameter("k", ProgramType::Int32)],
        None,
        false,
        Vec::new(),
        Vec::new(),
    );
    let function = adapter_reader("indexed_adapter_reader", cell.clone(), wide.clone())
        .with_composite_resource_definitions(vec![cell, decoy, wide]);
    let samples = [4, 16, 64].map(|count| {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let pointer = Address::symbolic(Variable(890_001));
        let owner = ResourceFact::own_composite(
            "wide".into(),
            vec![ProgramValue::pointer(pointer.clone())],
        );
        let frame = ResourceContext::new()
            .unchecked_with_facts(
                (0..count).map(|i| ResourceFact::own_composite("decoy".into(), vec![int32(i)])),
            )
            .unchecked_with_fact(owner);
        let caller = adapter_caller(&pointer).with_resource_context(frame);
        let callee = bind_program_function_arguments(
            &caller,
            &function,
            &[ProgramValue::pointer(pointer.clone())],
        )
        .expect("bind arguments");
        let (transfer, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepare_function_resource_transfer(
                &caller,
                &callee,
                &function,
                &assumptions,
                &mut ExecutionBudget::new(),
                false,
                ResourceTransitionPurpose::CallSite,
            )
            .expect("prepare call")
            .expect("held wide range supplies the cell view")
        });

        assert!(!caller.resources().facts_are_materialized());
        let plan = transfer.stable_view_plan.expect("one checked loan");
        assert_eq!(plan.stable_views().len(), 1);
        let tail = MemoryRange::new(pointer, 1u32.into(), 2u32.into());
        assert_eq!(
            plan.ledger.permits_memory_access(&tail),
            Err(LoanRefusal::ActiveDependency)
        );
        work
    });
    assert_eq!(samples, [samples[0]; 3]);
}

#[test]
fn preparing_a_reserved_fold_leaves_unrelated_caller_heads_unmaterialized() {
    use crate::kernel::program_expression::{int32_literal, variable};

    let function = program_function(
        ProgramType::Void,
        "accept_cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(program_void_value()),
    )
    .with_resource_summary(
        vec![ResourceSpec::composite(
            ResourceAccessMode::Own,
            "cell".into(),
            vec![variable("p")],
            vec![ProgramType::Int32Pointer],
        )],
        vec![],
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    )]);
    let heap = |id| Address {
        base: AddressBase::Heap(id),
        offset: AddressOffset::Constant(0),
    };
    let cell =
        |id| ResourceFact::own_composite("cell".into(), vec![ProgramValue::pointer(heap(id))]);
    let samples = [16, 64, 256].map(|extras| {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let mut resources = ResourceContext::new_with_equalities(&facts);
        let mut memory = SymbolicMemory::new();
        for id in 0..=extras {
            memory = memory
                .with_heap_allocation_claim(
                    heap(id),
                    AllocationSize::int32(MachineTerm::constant(4)),
                )
                .expect("distinct live cell");
            resources = resources.unchecked_with_fact(cell(id));
        }
        let caller = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(resources);
        let callee = caller
            .clone()
            .with_local("p", ProgramValue::pointer(heap(0)));
        let (transfer, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepare_function_resource_transfer(
                &caller,
                &callee,
                &function,
                &facts,
                &mut ExecutionBudget::new(),
                false,
                ResourceTransitionPurpose::CallSite,
            )
            .expect("prepare call")
            .expect("caller supplies the exact declared fold")
        });
        assert!(!caller.resources().facts_are_materialized());
        assert!(
            transfer
                .callee_resources
                .contains_exact_representation(&cell(0))
        );
        assert!(
            !transfer
                .caller_resources_after_requirements
                .contains_exact_representation(&cell(0))
        );
        assert!(
            transfer
                .caller_resources_after_requirements
                .contains_exact_representation(&cell(1))
        );
        work
    });
    assert_eq!(samples, [samples[0]; 3]);
}

#[test]
fn verified_call_loan_requirement_building_does_not_visit_live_loans() {
    let effects = [MemoryRange::new(pointer(), 0u32.into(), 1u32.into())];
    let samples = [4, 16, 64].map(|count| {
        let mut ledger = LoanLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        for i in 0..count {
            ledger = lend_summary_test_range(
                &ledger,
                lender,
                reader,
                MemoryRange::new(
                    Address::symbolic(Variable(93_000 + i)),
                    0u32.into(),
                    1u32.into(),
                ),
            );
        }
        let memory = SymbolicMemory::new();
        let (requirements, work) = crate::instrumentation::measure_deterministic_work(|| {
            verified_call_loan_requirements(
                Some(&ledger),
                &effects,
                || CallRequirementSite::for_requirement("write", "write", 0, &[], &memory),
                0,
                "verified call allocation retirement separation",
            )
        });
        assert_eq!(requirements.len(), 1);
        work
    });
    assert_eq!(samples, [samples[0]; 3]);
}

#[test]
fn local_storage_classification_stops_at_a_fixed_ownership_gap() {
    let mut curves = Vec::new();
    for case in ["implicit", "gap", "owner", "joined"] {
        let mut samples = Vec::new();
        for count in [4u32, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = pointer();
            let facts = PureFactContext::new();
            let own = |start: u32, end: u32| {
                ResourceFact::own_memory(MemoryRange::new(
                    pointer.clone(),
                    start.into(),
                    end.into(),
                ))
            };
            let mut resources = ResourceContext::new_with_equalities(&facts);
            if case != "implicit" {
                resources = resources.unchecked_with_fact(own(
                    0,
                    if case == "owner" {
                        1024
                    } else if case == "joined" {
                        512
                    } else {
                        1
                    },
                ));
            }
            if case == "joined" {
                resources = resources.unchecked_with_fact(own(512, 1024));
            }
            for index in 0..count {
                // The gap at cell 1 and the requested 1024-cell view stay fixed.
                // Complete-owner controls put extras beyond the request.
                let start = if case == "gap" { 100 } else { 2048 } + 2 * index;
                resources = resources.unchecked_with_fact(if case == "implicit" {
                    ResourceFact::own_token("unrelated".into(), vec![int32(index)])
                } else {
                    own(start, start + 1)
                });
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new()
                .with_population_creation_tracking()
                .with_memory(with_initialized_cells(
                    SymbolicMemory::new().with_block(pointer.base.clone(), 16384),
                    &pointer,
                    1024,
                ))
                .with_resource_context(resources);
            let function = reader_for_input("classify_local_storage", 1024);
            let environment = environment(&function);
            let arguments = [crate::kernel::program_expression::pointer_value(
                pointer.clone(),
            )];
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((paths, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        execute_program_function_call_paths(
                            &state,
                            &function,
                            &arguments,
                            &facts,
                            ExecutionContext::verify_loops(&environment),
                            &mut ExecutionBudget::new(),
                        )
                        .expect("classification produces a call outcome")
                    })
                });
                let succeeds = matches!(
                    paths.as_slice(),
                    [FunctionPath {
                        outcome: FunctionOutcome::Return { .. },
                        ..
                    }]
                );
                assert_eq!(
                    succeeds,
                    matches!(case, "implicit" | "owner"),
                    "{case}/{count}: {paths:?}"
                );
                let callee = state
                    .clone()
                    .with_local("p", ProgramValue::pointer(pointer.clone()));
                let ((transfer, transfer_work), transfer_maps) =
                    crate::persistent::measure_persistent_work(|| {
                        crate::instrumentation::measure_deterministic_work(|| {
                            prepare_function_resource_transfer(
                                &state,
                                &callee,
                                &function,
                                &facts,
                                &mut ExecutionBudget::new(),
                                false,
                                ResourceTransitionPurpose::CallSite,
                            )
                            .expect("transfer preparation produces a verdict")
                        })
                    });
                assert_eq!(transfer.is_ok(), matches!(case, "implicit" | "owner"));
                queries.push((work, maps, transfer_work, transfer_maps));
            }
            samples.push((count, queries));
        }
        eprintln!("local storage {case}, full-call/transfer work+maps: {samples:?}");
        curves.push((case, samples));
    }
    // Bound both preparation and completion, including the complete owner.
    for (case, samples) in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.2 <= small.2 + 128
                    && big.3 <= small.3 * 3 + 512
                    && (big.0 <= small.0 + 128 && big.1 <= small.1 * 3 + 512)),
            "local-storage classification scans rejected fragments ({case}): {samples:?}"
        );
    }
}

/// A read-only call borrows one complete owner and returns it unchanged.
/// Increasing the disjoint caller frame must not increase completion work.
#[test]
fn returning_one_borrowed_owner_does_not_rebuild_its_memory_block() {
    let mut curves = Vec::new();
    for count in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = pointer();
        let facts = PureFactContext::new();
        let own = |start: u32, end: u32| {
            ResourceFact::own_memory(MemoryRange::new(pointer.clone(), start.into(), end.into()))
        };
        let owner = own(0, 1024);
        let mut resources =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner.clone());
        for index in 0..count {
            resources = resources.unchecked_with_fact(own(2048 + 2 * index, 2049 + 2 * index));
        }
        resources.synchronize_memory_equalities(&facts);
        let state = ExecutionState::new()
            .with_population_creation_tracking()
            .with_memory(with_initialized_cells(
                SymbolicMemory::new().with_block(pointer.base.clone(), 16384),
                &pointer,
                1024,
            ))
            .with_resource_context(resources);
        let function = reader_for_input("return_one_owner", 1024);
        let environment = environment(&function);
        let callee = state
            .clone()
            .with_local("p", ProgramValue::pointer(pointer.clone()));
        let mut samples = Vec::new();
        for _ in 0..3 {
            let ((paths, call_work), call_maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        execute_program_function_call_paths(
                            &state,
                            &function,
                            &[crate::kernel::program_expression::pointer_value(
                                pointer.clone(),
                            )],
                            &facts,
                            ExecutionContext::verify_loops(&environment),
                            &mut ExecutionBudget::new(),
                        )
                        .unwrap()
                    })
                });
            let [
                FunctionPath {
                    outcome:
                        FunctionOutcome::Return {
                            state: returned, ..
                        },
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("the read-only call must return: {paths:?}");
            };
            let ((transfer, entry_work), entry_maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        prepare_function_resource_transfer(
                            &state,
                            &callee,
                            &function,
                            &facts,
                            &mut ExecutionBudget::new(),
                            false,
                            ResourceTransitionPurpose::CallSite,
                        )
                        .unwrap()
                        .unwrap()
                    })
                });
            let plan = transfer.stable_view_plan.as_ref().unwrap();
            let ((recovery, recovery_work), recovery_maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        plan.clone()
                            .recover_stable_views(&facts, &BTreeMap::new(), &[])
                            .unwrap()
                    })
                });
            for result in [returned.resources(), &recovery.resources] {
                assert!(result.contains_exact_representation(&owner));
                for index in 0..count {
                    assert!(
                        result.contains_exact_representation(&own(
                            2048 + 2 * index,
                            2049 + 2 * index
                        ))
                    );
                }
            }
            assert!(state.resources().contains_exact_representation(&owner));
            samples.push([
                (call_work, call_maps),
                (entry_work, entry_maps),
                (recovery_work, recovery_maps),
            ]);
        }
        curves.push((count, samples));
    }
    eprintln!("call/entry/recovery work+maps: {curves:?}");
    for phase in [0, 1, 2] {
        assert!(
            curves[3]
                .1
                .iter()
                .zip(&curves[0].1)
                .all(|(large, small)| large[phase].0 <= small[phase].0 + 128
                    && large[phase].1 <= small[phase].1 * 3 + 512),
            "completion scans the unrelated frame, phase {phase}: {curves:?}"
        );
    }
}

/// Restoring entry borrows pays for its returned facts, not aliases or
/// unrelated owners. Each query forks the same prepared residual frame.
#[test]
fn call_borrow_restoration_ignores_ambient_aliases_and_frame() {
    let symbolic = |id| Address {
        base: AddressBase::Symbolic(Variable(id)),
        offset: AddressOffset::Constant(0),
    };
    let own = |base| ResourceFact::own_memory(MemoryRange::new(base, 0u32.into(), 4u32.into()));
    for axis in ["aliases", "frame"] {
        let mut samples = Vec::new();
        for count in [4_u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let selected = symbolic(881_000);
            let facts = (0..if axis == "aliases" { count } else { 0 }).fold(
                PureFactContext::new(),
                |facts, index| {
                    facts.assume_condition(
                        ConditionTerm::address_equal(selected.clone(), symbolic(882_000 + index)),
                        true,
                    )
                },
            );
            let returned = own(selected);
            let mut source = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_fact(own(symbolic(883_000)))
                .unchecked_with_fact(returned.clone());
            if axis == "frame" {
                for index in 0..count {
                    source = source.unchecked_with_fact(own(symbolic(884_000 + index)));
                }
            }
            assert!(source.validity_error(&facts).is_none());
            let source_count = source.facts().len();
            let frame = source
                .clone()
                .without_fact_incrementally(&returned, &facts)
                .unwrap();
            frame.synchronize_memory_equalities(&facts);
            let outputs =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(returned.clone());
            let mut runs = Vec::new();
            for _ in 0..3 {
                let ((joined, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        ResourceContext::restore_call_borrows(
                            ReturnedCallBorrows {
                                frame: frame.clone(),
                                outputs: outputs.clone(),
                            },
                            &facts,
                        )
                    })
                });
                let (joined, occurrences) = joined.unwrap();
                assert_eq!(occurrences.len(), 1);
                assert_eq!(joined.facts().len(), source_count);
                assert_eq!(source.facts().len(), source_count);
                assert_eq!(frame.facts().len(), source_count - 1);
                assert_eq!(occurrences[0].0, returned);
                runs.push((work, maps));
            }
            samples.push((count, runs));
        }
        eprintln!("call borrow restoration {axis}: {samples:?}");
        for (_, runs) in &samples {
            for (run, baseline) in runs.iter().zip(&samples[0].1) {
                assert!(
                    run.0 <= baseline.0 + 64 && run.1 <= baseline.1 * 3 + 512,
                    "{axis}: {samples:?}"
                );
            }
        }
    }
}

fn check_produced_call_return_lowering(axis: &str, overlap: bool) {
    let symbolic = |id| Address::symbolic(Variable(id));
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let selected = symbolic(8_910_000);
        let neighbor = symbolic(8_920_000);
        let mut facts = PureFactContext::new().assume_condition(
            ConditionTerm::address_equal(selected.clone(), neighbor.clone()),
            true,
        );
        for index in 1..count {
            if axis != "owners" {
                facts = facts.assume_condition(
                    ConditionTerm::address_equal(
                        if axis == "aliases" {
                            selected.clone()
                        } else {
                            symbolic(8_930_000)
                        },
                        symbolic(8_940_000 + index),
                    ),
                    true,
                );
            }
        }
        let start = u32::from(!overlap);
        let mut resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(neighbor, start.into(), (start + 1).into())),
        );
        if axis == "owners" {
            for index in 0..count {
                resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                    MemoryRange::new(symbolic(8_950_000 + index), 0u32.into(), 1u32.into()),
                ));
            }
        }
        resources.synchronize_memory_equalities(&facts);
        let state = ExecutionState::new()
            .with_population_creation_tracking()
            .with_memory(SymbolicMemory::new().with_block(selected.base.clone(), 8))
            .with_resource_context(resources);
        let output = ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
        let function = program_function(
            ProgramType::Void,
            "produce_one_cell",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            program_skip(),
        )
        .with_resource_summary(vec![], vec![output]);
        let environment =
            ExecutionEnvironment::new().with_external_function_rule(ExternalFunctionRule {
                function: function.clone(),
                scoped_unselected: false,
                representation_copy: None,
            });
        let arguments = [crate::kernel::program_expression::pointer_value(
            selected.clone(),
        )];
        let execute = || {
            let _operation = crate::kernel::search::FastOperationScope::enter(
                "constant produced ownership call",
            );
            execute_program_function_call_paths(
                &state,
                &function,
                &arguments,
                &facts,
                ExecutionContext::apply_verified_rules(&environment),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        };
        let ((paths, work), events) = crate::instrumentation::collect(|| {
            crate::instrumentation::measure_deterministic_work(execute)
        });
        let phases = events
            .iter()
            .filter_map(|event| match event {
                crate::instrumentation::VerificationEvent::OperationFinished {
                    name, work, ..
                } if name.starts_with("ensured resource")
                    || name == "ensured composite frontier check" =>
                {
                    Some((name.as_str(), *work))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        eprintln!("call phases {axis}/{overlap}/{count}: {phases:?}");
        let succeeds = matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::Return { .. },
                ..
            }]
        );
        assert_eq!(succeeds, !overlap, "{axis}/{count}: {paths:?}");
        let lowering_work = phases
            .iter()
            .find(|(name, _)| *name == "ensured resource lowering")
            .unwrap()
            .1;
        samples.push((count, work, lowering_work));
    }
    eprintln!(
        "produced ownership call axis={axis}, overlap={overlap}, (count,total,lowering): {samples:?}"
    );
    for (_, total, work) in &samples {
        assert!(
            *total <= samples[0].1 + 32,
            "whole call scans {axis}: {samples:?}"
        );
        assert!(
            *work <= samples[0].2 + 16,
            "return construction scans {axis}: {samples:?}"
        );
    }
}

#[test]
fn produced_call_return_aliases_success() {
    check_produced_call_return_lowering("aliases", false);
}

#[test]
fn produced_call_return_aliases_overlap_refusal() {
    check_produced_call_return_lowering("aliases", true);
}

#[test]
fn produced_call_return_owners_success() {
    check_produced_call_return_lowering("owners", false);
}

#[test]
fn produced_call_return_owners_overlap_refusal() {
    check_produced_call_return_lowering("owners", true);
}

#[test]
fn produced_call_return_unrelated_aliases_success() {
    check_produced_call_return_lowering("unrelated_aliases", false);
}

#[test]
fn produced_call_return_unrelated_aliases_overlap_refusal() {
    check_produced_call_return_lowering("unrelated_aliases", true);
}
