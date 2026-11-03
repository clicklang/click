// Full-call controls for implicit local-storage classification.
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
            let state = CState::new()
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
                    .with_local("p", CValue::pointer(pointer.clone()));
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
    // The complete-owner call still has a separate post-entry scan. Retain
    // its measured curve here; only transfer preparation is bounded for it.
    for (case, samples) in curves {
        assert!(
            samples[3]
                .1
                .iter()
                .zip(&samples[0].1)
                .all(|(big, small)| big.2 <= small.2 + 128
                    && big.3 <= small.3 * 3 + 512
                    && (case == "owner" || (big.0 <= small.0 + 128 && big.1 <= small.1 * 3 + 512))),
            "local-storage classification scans rejected fragments ({case}): {samples:?}"
        );
    }
}
