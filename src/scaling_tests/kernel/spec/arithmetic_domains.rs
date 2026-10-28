fn division_paths(context: &PureFactContext) -> Vec<CExpressionPath> {
    apply_spec_arithmetic(
        CValue::UInt32(Bitvector32Term::UInt32Constant(7)),
        CValue::UInt32(Bitvector32Term::Variable(Variable(690_000))),
        ExecutionFacts::default(),
        Vec::new(),
        context,
        apply_c_divide,
    )
}

fn value_path(paths: Vec<CExpressionPath>) -> Option<CExpressionPath> {
    paths
        .into_iter()
        .find(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
}

#[test]
fn impossible_arithmetic_keeps_its_term_without_scanning_the_parent() {
    let zero = ConditionTerm::uint32_equal(
        Bitvector32Term::Variable(Variable(690_000)),
        Bitvector32Term::UInt32Constant(0),
    );
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let expected = value_path(division_paths(&PureFactContext::new()))
            .unwrap()
            .outcome;
        let mut base = PureFactContext::new();
        for index in 0..size {
            base = base.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(691_000 + index)),
                    Bitvector32Term::Constant(1000),
                ),
                true,
            );
        }
        let parent = base.clone().assume_condition(zero.clone(), true);
        let nonzero = base.assume_condition(zero.clone(), false);
        let impossible = parent.clone().assume_condition(zero.clone(), false);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(
                    value_path(division_paths(&parent)).is_none(),
                    "a reachable zero divisor remains undefined"
                );
                assert_eq!(
                    value_path(division_paths(&nonzero)).unwrap().outcome,
                    expected
                );
                let unreachable = value_path(division_paths(&impossible))
                    .expect("an impossible symbolic division retains its term");
                assert_eq!(unreachable.outcome, expected);
                assert!(unreachable.facts.is_empty());
                assert!(unreachable.obligations.is_empty());
            }
        });
        samples.push((size, work));
    }
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 16),
        "arithmetic domain work: {samples:?}"
    );
}
