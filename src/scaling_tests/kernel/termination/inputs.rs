#[test]
fn completed_input_selection_and_consumption_ignore_unrelated_source_and_bodies() {
    for size in [1, 16, 64, 256, 1024] {
        let (root, execution) = ranked_body(size);
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution, vec![]).publish(false);
        attempt.commit();
        let body = root.finish().unwrap();
        let mut inputs = TerminationBodyInputs::completed(&[body], &[], &BTreeMap::new());
        // Retain a conservative recursive edge, as a declaration can even
        // when the ordinary proof avoids executing that edge.
        inputs.rules[0].checked_callees = Some(Arc::new(BTreeSet::from(["concrete_body".into()])));
        let selected = inputs.completed["concrete_body"].clone();
        for index in 0..size {
            inputs
                .completed
                .insert(format!("unrelated{index}"), selected.clone());
        }
        let (local, work) =
            crate::instrumentation::measure_deterministic_work(|| inputs.local("concrete_body"));
        assert!(matches!(local, LocalTerminationInput::Completed(_)));
        assert!(work <= 4, "{size}: {work} selected-input work");
        let plans = [program_function_termination_plan(
            "concrete_body",
            Some(FunctionTerminationMeasure::Expression("0".into())),
            BTreeMap::new(),
        )];
        let goals = super::super::super::obligations::TerminationObligations::generate_from_inputs(
            &inputs,
            &plans,
            &BTreeMap::new(),
            &[],
            &program_termination_height_plan(&inputs.rules, &[]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            false,
            None,
        )
        .unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            goals.prove_local_descent(&"concrete_body".into())
        });
        assert!(result.unwrap().is_none());
        assert!(work <= 8, "{size}: {work} completed-body consumption work");
    }
}
