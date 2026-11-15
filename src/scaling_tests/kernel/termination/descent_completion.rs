#[test]
fn descent_step_membership_is_independent_of_unrelated_declarations() {
    let function = function();
    for size in [1, 16, 64, 256, 1024] {
        let mut environment = environment(&function);
        for index in 0..size {
            environment = environment.with_function(ProgramFunction::new(
                ProgramType::Void,
                format!("unrelated_{index}"),
                vec![],
                ProgramStatement::Skip,
            ));
        }
        let opened = OpenedDescent::open(&function, &environment)
            .unwrap()
            .unwrap();
        let step = DescentStep::under(&environment);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| opened.accept(step.as_ref()));
        result.unwrap();
        assert!(work <= 2, "{size}: {work} descent-step work");
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| opened.accept(None));
        assert!(result.is_err());
        assert!(work <= 2, "{size}: {work} refusal work");
    }
}

#[test]
fn termination_consumes_completed_descent_without_walking_unrelated_source() {
    for size in [1, 16, 64, 256, 1024] {
        let (root, execution) = ranked_body(size);
        let attempt = root.begin_attempt();
        completed_body(attempt.root(), execution, vec![]).publish(false);
        attempt.commit();
        let mut rule = root.finish().unwrap().into_rule().unwrap();
        // A conservative dependency may retain a recursive edge even when
        // the proof avoids it. The completed ordinary proof already owns its
        // descent; the consumer must not revisit the body to rediscover it.
        rule.checked_callees = Some(Arc::new(BTreeSet::from(["concrete_body".into()])));
        let plans = [program_function_termination_plan(
            "concrete_body",
            Some(FunctionTerminationMeasure::Expression("0".into())),
            BTreeMap::new(),
        )];
        let rules = [rule];
        let goals = super::super::super::obligations::TerminationObligations::generate(
            &rules,
            &plans,
            &BTreeMap::new(),
            &[],
            &program_termination_height_plan(&rules, &[]),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            false,
        )
        .unwrap();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            goals.prove_local_descent(&"concrete_body".into())
        });
        assert!(result.unwrap().is_none());
        assert!(work <= 16, "{size}: {work} descent-consumption work");
    }
}

#[test]
fn descent_step_membership_does_not_compare_growing_measure_tuples() {
    for size in [1, 8, 64, 256] {
        let function = function().with_recursion_measure(vec![
            RankingComponent::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            );
            size
        ]);
        let environment = environment(&function);
        let opened = OpenedDescent::open(&function, &environment)
            .unwrap()
            .unwrap();
        let step = DescentStep::under(&environment);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| opened.accept(step.as_ref()));
        result.unwrap();
        assert!(
            work <= 2,
            "{size} measure members: {work} context-membership work"
        );
    }
}
