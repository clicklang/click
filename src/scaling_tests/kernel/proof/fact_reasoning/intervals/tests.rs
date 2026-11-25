#[test]
fn one_operation_interval_check_ignores_ambient_related_and_unrelated_facts() {
    let (goal, bounds) = inputs(MachineBinaryOp::Add, 1);
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut ambient = bounds.clone();
            for index in 0..size {
                let subject = observe(OldMachineTerm::Variable(Variable(if related {
                    987_701
                } else {
                    988_000 + index
                })));
                ambient.push(le(literal(-1000 - index as i64), subject));
            }
            let facts = PureFactStore::from_ordered(&ambient);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                normalize_using_conditions(&goal, &bounds, &facts)
            });
            result.unwrap();
            assert!(normalize_using_conditions(&goal, &bounds[..1], &facts).is_err());
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples.iter().all(|work| *work <= 2 * samples[0]),
            "ambient scan: {samples:?}"
        );
    }
}
#[test]
fn one_operation_interval_work_tracks_only_explicit_premises() {
    let (goal, bounds) = inputs(MachineBinaryOp::Add, 1);
    let samples = [4, 16, 64].map(|size| {
        let mut selected = bounds.clone();
        for index in 0..size {
            selected.push(le(
                literal(-100),
                observe(OldMachineTerm::Variable(Variable(988_000 + index))),
            ));
        }
        let facts = PureFactStore::from_ordered(&selected);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_using_conditions(&goal, &selected, &facts)
        });
        result.unwrap();
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "superlinear explicit-input work: {samples:?}"
    );
}

#[test]
fn paired_endpoints_share_selected_input_work() {
    let x = observe(OldMachineTerm::Variable(Variable(989_700)));
    let exact: SharedIntegerTerm =
        IntegerTerm::add(x.as_ref().clone(), IntegerTerm::constant_i64(1)).into();
    let goal = le(exact.clone(), literal(11));
    let pair = Proposition::And(Box::new(goal.clone()), Box::new(goal.clone()));
    let mut extra_work = Vec::new();
    for size in [4, 16, 64] {
        let mut selected = vec![le(literal(0), x.clone()), le(x.clone(), literal(10))];
        for index in 0..size {
            selected.push(le(
                observe(OldMachineTerm::Variable(Variable(989_800 + index))),
                literal(20),
            ));
        }
        let (single, one) = crate::instrumentation::measure_deterministic_work(|| {
            reduces_one_operation(&goal, &selected)
        });
        let (paired, two) = crate::instrumentation::measure_deterministic_work(|| {
            reduces_one_operation(&pair, &selected)
        });
        assert!(single && paired);
        extra_work.push(two.saturating_sub(one));
        let wrong = Proposition::And(
            Box::new(goal.clone()),
            Box::new(le(exact.clone(), literal(10))),
        );
        assert!(!reduces_one_operation(&wrong, &selected));
    }
    assert!(
        extra_work.iter().all(|work| *work <= extra_work[0] + 8),
        "{extra_work:?}"
    );
}
