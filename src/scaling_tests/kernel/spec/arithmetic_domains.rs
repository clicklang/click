fn division_paths(context: &PureFactContext) -> Vec<CExpressionPath> {
    apply_spec_arithmetic(
        crate::kernel::MachineBinaryOp::Divide,
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
                let undefined = value_path(division_paths(&parent)).unwrap();
                assert_eq!(undefined.outcome, expected);
                assert_eq!(undefined.obligations.len(), 1);
                assert!(!parent.proves_exact(undefined.obligations[0].proposition()));
                assert_eq!(
                    value_path(division_paths(&nonzero)).unwrap().outcome,
                    expected
                );
                let unreachable = value_path(division_paths(&impossible))
                    .expect("an impossible symbolic division retains its term");
                assert_eq!(unreachable.outcome, expected);
                assert!(unreachable.facts.is_empty());
                assert_eq!(unreachable.obligations.len(), 1);
                assert!(impossible.contains_assumed_exact(&Proposition::ConditionIs(
                    ConditionTerm::Constant(false),
                    true
                )));
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
                    right: SpecExpression::Value(crate::kernel::uint8(255u32)),
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

#[test]
fn structural_signed_addition_keeps_its_debt_independent_of_ambient_facts() {
    fn sample(claims: u64, related: u64, unrelated: u64) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Bitvector32Term::Variable(Variable(696_000));
        let mut context = PureFactContext::new();
        for i in 0..related {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(variable.clone(), (1000 + i as u32).into()),
                true,
            );
        }
        for i in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(697_000 + i)),
                    1000u32.into(),
                ),
                true,
            );
        }
        let overflow = ConditionTerm::signed_add_overflows(variable.clone(), 1u32.into());
        context = context.assume_condition(overflow.clone(), false);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..claims {
                let paths = apply_spec_arithmetic(
                    crate::kernel::MachineBinaryOp::Add,
                    int32(variable.clone()),
                    int32(1u32),
                    ExecutionFacts::default(),
                    Vec::new(),
                    &context,
                    |left, right, facts, obligations, context| {
                        apply_c_add(
                            &CState::new(),
                            left,
                            right,
                            None,
                            None,
                            facts,
                            obligations,
                            context,
                        )
                    },
                );
                assert_eq!(paths.len(), 1);
                assert_eq!(
                    paths[0].outcome,
                    CExpressionOutcome::Value(int32(Bitvector32Term::add(
                        variable.clone(),
                        1u32.into()
                    ),))
                );
                assert!(paths[0].facts.is_empty());
                assert_eq!(paths[0].obligations.len(), 1);
                assert_eq!(
                    paths[0].obligations[0].proposition(),
                    &Proposition::signed_arithmetic_domain(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Add,
                        &variable,
                        &Bitvector32Term::Constant(1),
                    )
                );
            }
        });
        work
    }
    let base = sample(4, 4, 4);
    for size in [4, 16, 64, 256] {
        assert!(sample(4, size, 4) <= base + 16);
        assert!(sample(4, 4, size) <= base + 16);
        assert!(sample(size, 4, 4) <= (base + 16) * size as usize / 4);
    }
}

#[test]
fn logical_shift_shape_and_work_ignore_ambient_count_facts() {
    let count = Bitvector32Term::Variable(Variable(696_000));
    let invalid =
        ConditionTerm::uint64_greater_equal(count.clone(), Bitvector32Term::UInt64Constant(32));
    let lower = |context: &PureFactContext| {
        apply_spec_arithmetic(
            crate::kernel::MachineBinaryOp::ShiftRight,
            CValue::UInt32(Bitvector32Term::Variable(Variable(696_001))),
            CValue::UInt64(count.clone()),
            ExecutionFacts::default(),
            Vec::new(),
            context,
            apply_c_shift_right,
        )
    };
    let expected = lower(&PureFactContext::new());
    assert_eq!(expected.len(), 1);
    assert_eq!(expected[0].obligations.len(), 1);
    let mut samples = Vec::new();
    for size in [32, 128, 512] {
        let mut base = PureFactContext::new();
        for i in 0..size {
            base = base.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(697_000 + i)),
                    Bitvector32Term::Constant(1000),
                ),
                true,
            );
        }
        let defined = base.clone().assume_condition(invalid.clone(), false);
        let undefined = base.assume_condition(invalid.clone(), true);
        let contradictory = undefined.clone().assume_condition(invalid.clone(), false);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for context in [&defined, &undefined, &contradictory] {
                let actual = lower(context);
                assert_eq!(actual.len(), 1);
                assert_eq!(actual[0].outcome, expected[0].outcome);
                assert_eq!(actual[0].obligations.len(), 1);
                assert_eq!(
                    actual[0].obligations[0].proposition(),
                    expected[0].obligations[0].proposition()
                );
                assert!(actual[0].facts.is_empty());
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn wide_logical_product_keeps_operands_when_equalities_grow() {
    let operand = Bitvector32Term::Variable(Variable(698_000));
    let lower = |context: &PureFactContext| {
        apply_spec_arithmetic(
            crate::kernel::MachineBinaryOp::Multiply,
            CValue::Int128(Bitvector32Term::Variable(Variable(698_001))),
            CValue::Int64(operand.clone()),
            ExecutionFacts::default(),
            Vec::new(),
            context,
            apply_c_multiply,
        )
    };
    let expected = lower(&PureFactContext::new());
    assert_eq!(expected.len(), 1);
    assert_eq!(expected[0].obligations.len(), 1);
    let mut samples = Vec::new();
    for size in [32, 128, 512] {
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::int64_equal(
                    Bitvector32Term::Variable(Variable(699_000 + i)),
                    Bitvector32Term::Int64Constant(i as i64),
                ),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::int64_equal(operand.clone(), Bitvector32Term::Int64Constant(0)),
            true,
        );
        let (actual, work) = crate::instrumentation::measure_deterministic_work(|| lower(&context));
        assert_eq!(actual.len(), 1);
        assert_eq!(actual[0].outcome, expected[0].outcome);
        assert_eq!(actual[0].obligations.len(), 1);
        assert!(actual[0].facts.is_empty());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn complete_arithmetic_domain_checks_ignore_related_alias_stars() {
    for established in [false, true] {
        let mut costs = Vec::new();
        for size in [0, 128, 512] {
            let _session = crate::kernel::VerificationSession::enter();
            let value = Bitvector32Term::Variable(Variable(780_000 + size * 4));
            let mut context = PureFactContext::new();
            for i in 0..size {
                context = context.assume_condition(ConditionTerm::equal(
                    value.clone(), Bitvector32Term::Variable(Variable(790_000 + i)),
                ), true);
            }
            if established {
                context = context.assume_condition(ConditionTerm::signed_less_than(
                    value.clone(), Bitvector32Term::Constant(i32::MAX as u32),
                ), true);
            }
            let domain = Proposition::signed_arithmetic_domain(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add, &value, &Bitvector32Term::Constant(1),
            );
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.settles_exactly(&domain)
            });
            assert_eq!(proved, established);
            costs.push(work);
        }
        assert!(costs.iter().all(|work| *work == costs[0]), "established={established}: {costs:?}");
    }
}
