#[test]
fn loop_control_destinations_ignore_unrelated_bodies_tails_and_parent_frames() {
    for continuing in [false, true] {
        for with_update in [false, true] {
            let mut measurements = Vec::new();
            for size in [4, 16, 64, 256] {
                let mut fixture =
                    nested_loop(continuing, false, with_update, size, size, size, false);
                let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                    transfer(&mut fixture, continuing)
                });
                assert_destination(&fixture, continuing, size);
                measurements.push(work);
            }
            assert!(
                measurements.iter().all(|work| *work <= measurements[0] + 8),
                "{continuing}/{with_update}: {measurements:?}"
            );
        }
    }
}

#[test]
fn loop_control_work_tracks_only_exited_scopes() {
    for continuing in [false, true] {
        let mut baseline = None;
        for scopes in [0, 4, 16, 64, 256] {
            let mut fixture = nested_loop(continuing, false, true, 2, 2, 2, false);
            for _ in 0..scopes {
                fixture
                    .core
                    .frontier
                    .continuations
                    .push(ProofExecutionContinuation {
                        loop_control: None,
                        remaining: Some(fixture.after_function.clone()),
                        next_statement_index: 99,
                        exceptional: None,
                    });
            }
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                transfer(&mut fixture, continuing)
            });
            assert_destination(&fixture, continuing, 2);
            let base = *baseline.get_or_insert(work);
            assert!(work >= base + scopes, "each exited scope is charged");
            assert!(
                work <= base + 4 * scopes + 8,
                "{scopes}: {work}, base {base}"
            );
        }
    }
}

#[test]
fn loop_phase_entry_ignores_unrelated_tail_and_locals() {
    for position in [
        crate::kernel::LoopTestPosition::BeforeBody,
        crate::kernel::LoopTestPosition::AfterBody,
    ] {
        let mut baseline = None;
        for size in [4, 16, 64, 256] {
            let statement = program_while(int32_literal(0), Vec::new(), ProgramStatement::Break)
                .with_loop_test(
                    ProgramStatement::LoopTest {
                        condition: int32_literal(0),
                        aggregate_steps: Vec::new(),
                    },
                    position,
                );
            let tail = (0..size).fold(ProgramStatement::Skip, |rest, _| {
                program_seq(program_assign("unrelated", int32_literal(7)), rest)
            });
            let source = Arc::new(program_seq(statement, tail));
            let function = ProgramFunction::new(
                ProgramType::Void,
                "entry_scaling",
                Vec::new(),
                (*source).clone(),
            );
            let state = (0..size).fold(ExecutionState::new(), |state, i| {
                state.with_local(format!("unused_{i}"), int32(i as u32))
            });
            let mut core = ExecutionProofCore::at_entry(
                state,
                ExecutionFrontier {
                    position: FrontierPosition::StatementEntry { remaining: source },
                    ..ExecutionFrontier::default()
                },
            );
            let (sources, work) = crate::instrumentation::measure_deterministic_work(|| {
                core.enter_loop_phases(&function, &[]).unwrap()
            });
            let base = *baseline.get_or_insert(work);
            assert!(
                work <= base + 8,
                "{position:?}, {size}: {work}, base {base}"
            );
            assert_eq!(sources.test_position, position);
            assert_eq!(core.execution_evidence[0].len(), 1);
        }
    }
}
