#[test]
fn shared_update_metadata_is_additive_in_continues_and_update_size() {
    for continues in [4, 16, 64, 256] {
        for update_size in [4, 16, 64, 256] {
            let body = (0..continues).fold(ProgramStatement::Skip, |body, _| {
                program_seq(
                    body,
                    program_if(
                        variable("choose"),
                        ProgramStatement::Continue,
                        ProgramStatement::Skip,
                    ),
                )
            });
            let update = (0..update_size).fold(ProgramStatement::Skip, |update, _| {
                program_seq(update, program_assign("i", int32_literal(1)))
            });
            let statement =
                program_while(int32_literal(0), Vec::new(), body).with_loop_update(update);
            let function =
                ProgramFunction::new(ProgramType::Void, "shared_update", Vec::new(), statement);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                function.prepare_loop_proofs();
            });
            assert!(
                work <= 100 * (continues + update_size) + 100,
                "{continues} continues, {update_size} update statements: {work}"
            );
        }
    }
}

#[test]
fn shared_test_metadata_is_additive_in_continues_and_test_size() {
    for continues in [4, 16, 64, 256] {
        for test_size in [4, 16, 64, 256] {
            let body = (0..continues).fold(ProgramStatement::Skip, |body, _| {
                program_seq(
                    body,
                    program_if(
                        variable("choose"),
                        ProgramStatement::Continue,
                        ProgramStatement::Skip,
                    ),
                )
            });
            let test = (0..test_size).fold(ProgramStatement::Skip, |test, _| {
                program_seq(test, program_assign("i", int32_literal(1)))
            });
            let statement = program_while(int32_literal(1), Vec::new(), body)
                .with_loop_test(test, LoopTestPosition::AfterBody);
            let function =
                ProgramFunction::new(ProgramType::Void, "shared_test", Vec::new(), statement);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                function.prepare_loop_proofs()
            });
            assert!(
                work <= 100 * (continues + test_size) + 100,
                "{continues} continues, {test_size} test statements: {work}"
            );
        }
    }
}

#[test]
fn loop_test_outcomes_ignore_unrelated_locals_and_track_selected_cleanup() {
    for truth in [false, true] {
        let mut unrelated_baseline = None;
        let mut cleanup_baseline = None;
        for size in [4, 16, 64, 256] {
            let state = (0..size).fold(ExecutionState::new(), |state, index| {
                state.with_local(format!("unrelated_{index}"), int32(index as u32))
            });
            for cleanup_size in [0, size] {
                let test = ProgramStatement::LoopTest {
                    condition: int32_literal(u32::from(truth)),
                    aggregate_steps: (0..cleanup_size as u32).collect(),
                };
                let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                    crate::kernel::eval::execute_execution_statement(
                        &state,
                        &test,
                        &PureFactContext::new(),
                    )
                    .expect("the test has one successor")
                });
                assert!(matches!(
                    (truth, outcome),
                    (true, StatementOutcome::Normal(_))
                        | (false, StatementOutcome::LoopTestFalse(_))
                ));
                if cleanup_size == 0 {
                    let baseline = *unrelated_baseline.get_or_insert(work);
                    assert!(
                        work <= baseline + 8,
                        "{size} unrelated locals: {work}, base {baseline}"
                    );
                } else {
                    let baseline = *cleanup_baseline.get_or_insert(work);
                    assert!(
                        work <= baseline + 8 * size + 16,
                        "{size} cleanup entries: {work}, base {baseline}"
                    );
                    assert!(work >= size, "each selected cleanup entry must be charged");
                }
            }
        }
    }
}
