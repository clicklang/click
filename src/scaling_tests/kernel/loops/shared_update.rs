#[test]
fn shared_update_metadata_is_additive_in_continues_and_update_size() {
    for continues in [4, 16, 64, 256] {
        for update_size in [4, 16, 64, 256] {
            let body = (0..continues).fold(ProgramStatement::Skip, |body, _| {
                program_seq(body, program_if(
                    variable("choose"), ProgramStatement::Continue, ProgramStatement::Skip,
                ))
            });
            let update = (0..update_size).fold(ProgramStatement::Skip, |update, _| {
                program_seq(update, program_assign("i", int32_literal(1)))
            });
            let statement = program_while(int32_literal(0), Vec::new(), body)
                .with_loop_update(update);
            let function = ProgramFunction::new(ProgramType::Void, "shared_update", Vec::new(), statement);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                function.prepare_loop_proofs();
            });
            assert!(work <= 100 * (continues + update_size) + 100,
                "{continues} continues, {update_size} update statements: {work}");
        }
    }
}

#[test]
fn shared_test_metadata_is_additive_in_continues_and_test_size() {
    for continues in [4, 16, 64, 256] {
        for test_size in [4, 16, 64, 256] {
            let body = (0..continues).fold(ProgramStatement::Skip, |body, _| {
                program_seq(body, program_if(variable("choose"), ProgramStatement::Continue, ProgramStatement::Skip))
            });
            let test = (0..test_size).fold(ProgramStatement::Skip, |test, _| {
                program_seq(test, program_assign("i", int32_literal(1)))
            });
            let statement = program_while(int32_literal(1), Vec::new(), body)
                .with_loop_test(test, LoopTestPosition::AfterBody);
            let function = ProgramFunction::new(ProgramType::Void, "shared_test", Vec::new(), statement);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| function.prepare_loop_proofs());
            assert!(work <= 100 * (continues + test_size) + 100,
                "{continues} continues, {test_size} test statements: {work}");
        }
    }
}
