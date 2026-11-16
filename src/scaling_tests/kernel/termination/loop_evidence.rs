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

#[test]
fn opening_nested_loop_coverage_is_linear_in_selected_source() {
    for size in [16, 64, 256, 512] {
        let body = (0..size).fold(ProgramStatement::Skip, |body, _| {
            crate::kernel::program_while(int32_literal(0), vec![], body)
        });
        let function = function(body);
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            PreparedLoopExits::open(&function).unwrap()
        });
        assert_eq!(plan.count, size);
        assert!(
            work <= 16 * size + 32,
            "{size} nested loops: {work} opening work"
        );
    }
}

#[test]
fn termination_consumes_concrete_exit_authority_without_walking_unrelated_body() {
    for size in [1, 16, 64, 256, 1024] {
        let (root, execution) = concrete_body(size);
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution, vec![]).publish(false);
        attempt.commit();
        let rule = root.finish().unwrap().to_reusable_rule().unwrap();
        let rules = [rule];
        let heights = program_termination_height_plan(&rules, &[]);
        let goals = super::super::super::obligations::TerminationObligations::generate_independent(
            &rules,
            &[],
            &BTreeMap::new(),
            &[],
            &heights,
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            false,
        )
        .unwrap();
        let (refusal, work) = crate::instrumentation::measure_deterministic_work(|| {
            goals
                .prove_local_descent(&"concrete_body".to_string())
                .unwrap()
        });
        assert!(refusal.is_none());
        assert!(
            work <= 16,
            "{size} unrelated body statements: {work} proof work"
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            prepare_independent_loop_exits(&rules, &BTreeMap::new())
        });
        assert!(
            work <= 4,
            "owned evidence must bypass the independent adapter: {work}"
        );
    }
}
