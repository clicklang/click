// Full-call controls for local-storage classification and escrow restoration.
use super::*;

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
                CResourceFact::own_memory(CMemoryRange::new(
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
                    CResourceFact::own_token("unrelated".into(), vec![int32(index)])
                } else {
                    own(start, start + 1)
                });
            }
            resources.synchronize_memory_equalities(&facts);
            let state = ExecutionState::new()
                .with_memory(
                    CMemory::new()
                        .with_block(pointer.block.clone(), 16384)
                        .store(pointer.clone(), int32(7)),
                )
                .with_resource_context(resources);
            let function = reader_for_input("classify_local_storage", 1024);
            let environment = environment(&function);
            let arguments = [c_pointer_value(pointer.clone())];
            let mut queries = Vec::new();
            for _ in 0..3 {
                let ((paths, work), maps) = crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        execute_c_function_call_paths(
                            &state,
                            &function,
                            &arguments,
                            &facts,
                            CExecutionContext::execute_bodies(&environment),
                            &mut ExecutionBudget::new(),
                        )
                        .expect("classification produces a call outcome")
                    })
                });
                let succeeds = matches!(
                    paths.as_slice(),
                    [CFunctionPath {
                        outcome: CFunctionOutcome::Return { .. },
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
            CResourceFact::own_memory(CMemoryRange::new(pointer.clone(), start.into(), end.into()))
        };
        let owner = own(0, 1024);
        let mut resources =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner.clone());
        for index in 0..count {
            resources = resources.unchecked_with_fact(own(2048 + 2 * index, 2049 + 2 * index));
        }
        resources.synchronize_memory_equalities(&facts);
        let state = ExecutionState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 16384)
                    .store(pointer.clone(), int32(7)),
            )
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
                        execute_c_function_call_paths(
                            &state,
                            &function,
                            &[c_pointer_value(pointer.clone())],
                            &facts,
                            CExecutionContext::execute_bodies(&environment),
                            &mut ExecutionBudget::new(),
                        )
                        .unwrap()
                    })
                });
            let [
                CFunctionPath {
                    outcome:
                        CFunctionOutcome::Return {
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
    let symbolic = |id| Pointer {
        block: PointerBlock::Symbolic(Variable(id)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let own = |base| CResourceFact::own_memory(CMemoryRange::new(base, 0u32.into(), 4u32.into()));
    for axis in ["aliases", "frame"] {
        let mut samples = Vec::new();
        for count in [4_u64, 16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let selected = symbolic(881_000);
            let facts = (0..if axis == "aliases" { count } else { 0 }).fold(
                PureFactContext::new(),
                |facts, index| {
                    facts.assume_condition(
                        ConditionTerm::pointer_equal(selected.clone(), symbolic(882_000 + index)),
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
