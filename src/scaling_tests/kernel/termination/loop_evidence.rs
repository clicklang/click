#[test]
fn selected_loop_opening_does_not_scan_unrelated_statements_or_loops() {
    for size in [1, 16, 64, 256, 1024] {
        let selected = loop_statement();
        let body = (0..size).fold(selected.clone(), |body, _| {
            ProgramStatement::seq(Arc::new(body), Arc::new(loop_statement()))
        });
        let function = function(body);
        let ((), setup_work) =
            crate::instrumentation::measure_deterministic_work(|| function.prepare_loop_proofs());
        assert!(
            setup_work <= 32 * size + 64,
            "{size}: {setup_work} setup work"
        );
        for index in [0, size] {
            let (opening, work) = crate::instrumentation::measure_deterministic_work(|| {
                function.open_loop_proof(index, selected.clone()).unwrap()
            });
            assert_eq!(opening.loop_evidence.as_ref().unwrap().index, index);
            assert!(
                work <= 16 * (size + 2).ilog2() as usize + 16,
                "{size}: {work} selected work"
            );
        }
        let mut wrong = selected.clone();
        let ProgramStatement::While { condition, .. } = &mut wrong else {
            unreachable!()
        };
        *condition = int32_literal(1);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            function.open_loop_proof(size, wrong)
        });
        assert!(result.is_err());
        assert!(
            work <= 16 * (size + 2).ilog2() as usize + 16,
            "{size}: {work} refusal work"
        );
    }
}

#[test]
fn opening_work_grows_with_the_selected_loop_body() {
    for size in [16, 64, 256, 1024] {
        let body = (0..size).fold(ProgramStatement::Skip, |body, _| {
            ProgramStatement::seq(Arc::new(body), Arc::new(ProgramStatement::Skip))
        });
        let selected = crate::kernel::program_while(int32_literal(0), Vec::new(), body);
        let function = function(selected.clone());
        function.prepare_loop_proofs();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            function.open_loop_proof(0, selected).unwrap()
        });
        assert!(
            work >= size,
            "{size}: missing selected-body charges ({work})"
        );
        assert!(work <= 8 * size + 32, "{size}: {work} selected-body work");
    }
}
