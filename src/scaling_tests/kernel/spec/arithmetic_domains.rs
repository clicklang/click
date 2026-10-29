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

#[test]
fn native_existential_domains_scale_with_claims_not_ambient_facts() {
    fn work(claims: u64, unrelated: u64) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for i in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(695_000 + i)),
                    1000u32.into(),
                ),
                true,
            );
        }
        let claim = |i| {
            let value = SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                694_000 + i,
            ))));
            SpecProposition::ExistsInt32 {
                name: "k".into(),
                variable: Variable(694_000 + i),
                body: Box::new(SpecProposition::Comparison {
                    left: SpecExpression::IntegerToMachine {
                        value: Box::new(SpecIntegerExpression::FromMachine(Box::new(value))),
                        destination: MachineIntegerType::UInt8,
                    },
                    operator: CComparisonOperator::Equal,
                    right: SpecExpression::Value(CValue::UInt8(255u32.into())),
                }),
            }
        };
        let proposition = (0..claims)
            .map(claim)
            .reduce(|left, right| SpecProposition::And(Box::new(left), Box::new(right)))
            .unwrap();
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::c_lower_spec_proposition_with_checked_obligations(
                &CState::new(),
                &proposition,
                None,
                &context,
            )
            .unwrap()
        });
        assert!(lowered.2.is_empty(), "witness debts escaped their binders");
        work
    }
    let selected: Vec<_> = [4, 16, 64, 256].map(|n| work(n, 0)).into();
    for pair in selected.windows(2) {
        assert!(pair[1] <= pair[0] * 5 + 256, "claims: {selected:?}");
    }
    let ambient: Vec<_> = [0, 16, 64, 256].map(|n| work(4, n)).into();
    assert!(
        ambient.iter().all(|n| *n <= ambient[0] + 64),
        "ambient facts: {ambient:?}"
    );
}
