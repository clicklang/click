#[test]
fn mirrored_float_spellings_use_exact_indexes_and_preserve_nan_polarity() {
    let left = MachineTerm::Variable(Variable(991701));
    let right = MachineTerm::Variable(Variable(991702));
    let comparison = |wide, operator, a: &MachineTerm, b: &MachineTerm, value| {
        let condition = FloatCondition::Comparison {
            operator,
            left: Box::new(a.clone()),
            right: Box::new(b.clone()),
        };
        Proposition::condition_is(
            if wide {
                ConditionTerm::Float64(condition)
            } else {
                ConditionTerm::Float32(condition)
            },
            value,
        )
    };
    use ComparisonOperator::*;
    for wide in [false, true] {
        for (operator, reversed) in [
            (Equal, Equal),
            (NotEqual, NotEqual),
            (LessThan, GreaterThan),
            (LessEqual, GreaterEqual),
            (GreaterThan, LessThan),
            (GreaterEqual, LessEqual),
        ] {
            for value in [false, true] {
                let goal = comparison(wide, operator, &left, &right, value);
                let held = comparison(wide, reversed, &right, &left, value);
                assert!(order_claim_equivalent(&goal, &held));
                assert!(!order_claim_equivalent(
                    &goal,
                    &comparison(!wide, reversed, &right, &left, value)
                ));
                assert!(!order_claim_equivalent(
                    &goal,
                    &comparison(wide, reversed, &right, &left, !value)
                ));
                let forms = order_claim_forms(&goal);
                assert_eq!(forms.len(), 4);
                assert!(forms.contains(&held));
                let mut baseline = None;
                for size in [0, 64, 256, 1024] {
                    let mut input = (0..size)
                        .map(|i| {
                            Proposition::condition_is(
                                ConditionTerm::Variable(Variable(992000 + i)),
                                true,
                            )
                        })
                        .collect::<Vec<_>>();
                    input.push(held.clone());
                    let facts = PureFactStore::from_ordered(&input);
                    let (available, work) =
                        crate::instrumentation::measure_deterministic_work(|| {
                            order_claim_forms(&goal)
                                .iter()
                                .any(|form| facts.contains(form))
                        });
                    assert!(available);
                    if let Some(first) = baseline {
                        assert!(
                            work <= first + 64,
                            "float alias lookup scanned {size} facts: {first} -> {work}"
                        );
                    } else {
                        baseline = Some(work);
                    }
                }
            }
        }
        let negated_le = comparison(wide, LessEqual, &left, &right, false);
        let greater = comparison(wide, GreaterThan, &left, &right, true);
        assert!(!order_claim_equivalent(&negated_le, &greater));
        assert!(!order_claim_forms(&negated_le).contains(&greater));
    }
}
