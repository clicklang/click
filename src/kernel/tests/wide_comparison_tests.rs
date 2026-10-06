use super::*;
use num_bigint::BigInt;

const LEFT: Variable = Variable(166_001);
const RIGHT: Variable = Variable(166_002);
const OPERATORS: [CComparisonOperator; 6] = [
    CComparisonOperator::Equal,
    CComparisonOperator::NotEqual,
    CComparisonOperator::LessThan,
    CComparisonOperator::LessEqual,
    CComparisonOperator::GreaterThan,
    CComparisonOperator::GreaterEqual,
];

fn compare(operator: CComparisonOperator, a: CExpression, b: CExpression) -> CExpression {
    match operator {
        CComparisonOperator::Equal => c_equal(a, b),
        CComparisonOperator::NotEqual => c_not_equal(a, b),
        CComparisonOperator::LessThan => c_less_than(a, b),
        CComparisonOperator::LessEqual => c_less_equal(a, b),
        CComparisonOperator::GreaterThan => c_greater_than(a, b),
        CComparisonOperator::GreaterEqual => c_greater_equal(a, b),
    }
}

fn condition(operator: CComparisonOperator, ty: MachineIntegerType) -> ConditionTerm {
    let a = IntegerTerm::from_machine(ty, Bitvector32Term::Variable(LEFT)).unwrap();
    let b = IntegerTerm::from_machine(ty, Bitvector32Term::Variable(RIGHT)).unwrap();
    match operator {
        CComparisonOperator::Equal => ConditionTerm::integer_equal(a, b),
        CComparisonOperator::NotEqual => ConditionTerm::integer_not_equal(a, b),
        CComparisonOperator::LessThan => ConditionTerm::integer_less_than(a, b),
        CComparisonOperator::LessEqual => ConditionTerm::integer_less_equal(a, b),
        CComparisonOperator::GreaterThan => ConditionTerm::integer_greater_than(a, b),
        CComparisonOperator::GreaterEqual => ConditionTerm::integer_greater_equal(a, b),
    }
}

fn complement(operator: CComparisonOperator) -> CComparisonOperator {
    match operator {
        CComparisonOperator::Equal => CComparisonOperator::NotEqual,
        CComparisonOperator::NotEqual => CComparisonOperator::Equal,
        CComparisonOperator::LessThan => CComparisonOperator::GreaterEqual,
        CComparisonOperator::LessEqual => CComparisonOperator::GreaterThan,
        CComparisonOperator::GreaterThan => CComparisonOperator::LessEqual,
        CComparisonOperator::GreaterEqual => CComparisonOperator::LessThan,
    }
}

fn symbolic(operator: CComparisonOperator, ty: MachineIntegerType) -> CExpression {
    let value = |variable| {
        CExpression::Value(match ty {
            MachineIntegerType::Int128 => CValue::Int128(Bitvector32Term::Variable(variable)),
            MachineIntegerType::UInt128 => CValue::UInt128(Bitvector32Term::Variable(variable)),
            _ => unreachable!(),
        })
    };
    compare(operator, value(LEFT), value(RIGHT))
}

fn paths(expression: &CExpression, context: &PureFactContext) -> Vec<CExpressionPath> {
    evaluate_c_expression_paths(
        &CState::new(),
        expression,
        context,
        &mut ExecutionBudget::for_c_expression(expression),
    )
    .unwrap()
}

fn outcome(expression: CExpression) -> CExpressionOutcome {
    let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

#[test]
fn wide_comparison_constants_match_full_width_ordering_oracle() {
    let high = BigInt::from(1u128 << 64);
    for (ty, values) in [
        (
            MachineIntegerType::Int128,
            vec![
                i128::MIN.into(),
                (-7).into(),
                (-1).into(),
                0.into(),
                1.into(),
                high.clone(),
                i128::MAX.into(),
            ],
        ),
        (
            MachineIntegerType::UInt128,
            vec![
                0.into(),
                1.into(),
                high.clone(),
                BigInt::from(1u128 << 127),
                u128::MAX.into(),
            ],
        ),
    ] {
        let literal = |value: &BigInt| {
            CExpression::Value(
                ty.constant_value(
                    MachineIntegerConstant::from_integer(ty.format(), value).unwrap(),
                )
                .unwrap(),
            )
        };
        for a in &values {
            for b in &values {
                for operator in OPERATORS {
                    let expected = match operator {
                        CComparisonOperator::Equal => a == b,
                        CComparisonOperator::NotEqual => a != b,
                        CComparisonOperator::LessThan => a < b,
                        CComparisonOperator::LessEqual => a <= b,
                        CComparisonOperator::GreaterThan => a > b,
                        CComparisonOperator::GreaterEqual => a >= b,
                    };
                    assert_eq!(
                        outcome(compare(operator, literal(a), literal(b))),
                        CExpressionOutcome::Value(int32(u32::from(expected))),
                        "{ty:?} {a} {operator:?} {b}"
                    );
                }
            }
        }
    }
}

#[test]
fn wide_comparison_symbolic_paths_retain_exact_true_and_false_guards() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for operator in OPERATORS {
            let expression = symbolic(operator, ty);
            let guard = condition(operator, ty);
            let output = paths(&expression, &PureFactContext::new());
            assert_eq!(output.len(), 2);
            for (path, truth) in output.iter().zip([true, false]) {
                assert_eq!(
                    path.outcome,
                    CExpressionOutcome::Value(int32(u32::from(truth)))
                );
                assert!(
                    path.facts.iter().any(|fact| fact.proposition()
                        == &Proposition::ConditionIs(guard.clone(), truth))
                );
                let context = PureFactContext::new().assume_condition(guard.clone(), truth);
                let known = paths(&expression, &context);
                assert_eq!(known.len(), 1);
                assert_eq!(known[0].outcome, path.outcome);
            }
            for truth in [true, false] {
                let context = PureFactContext::new()
                    .assume_condition(condition(complement(operator), ty), !truth);
                let known = paths(&expression, &context);
                assert_eq!(known.len(), 1);
                assert_eq!(
                    known[0].outcome,
                    CExpressionOutcome::Value(int32(u32::from(truth)))
                );
            }
            assert!(prove_c_expression_evaluation(CState::new(), expression).is_none());
        }
    }
}

#[test]
fn wide_comparison_requires_explicit_promotions_and_preserves_operand_failures() {
    for operator in OPERATORS {
        for (a, b) in [
            (c_int128_literal(7), c_uint128_literal(3)),
            (c_int128_literal(7), c_int64_literal(3)),
            (c_uint128_literal(7), c_int32_literal(3)),
            (c_uint128_literal(7), c_void_value()),
        ] {
            assert_eq!(
                outcome(compare(operator, a, b)),
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            );
        }
        let converted = c_integer_cast_modulo(c_int64_literal(-1), CType::UInt128);
        assert_eq!(
            outcome(compare(
                CComparisonOperator::GreaterThan,
                converted,
                c_uint128_literal(7)
            )),
            CExpressionOutcome::Value(int32(1))
        );
        for on_left in [false, true] {
            for (bad, expected) in [
                (
                    c_divide(c_int128_literal(1), c_int128_literal(0)),
                    CUndefinedBehavior::DivisionByZero,
                ),
                (
                    c_remainder(c_int128_literal(i128::MIN), c_int128_literal(-1)),
                    CUndefinedBehavior::SignedOverflow,
                ),
            ] {
                let good = c_int128_literal(0);
                let (a, b) = if on_left { (bad, good) } else { (good, bad) };
                assert_eq!(
                    outcome(compare(operator, a, b)),
                    CExpressionOutcome::UndefinedBehavior(expected)
                );
            }
        }
    }
}

#[test]
fn wide_comparison_queries_ignore_unrelated_ambient_facts() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for operator in OPERATORS {
            let expression = symbolic(operator, ty);
            // Exercise the second indexed query rather than the direct key.
            let guard = condition(complement(operator), ty);
            let mut samples = Vec::new();
            for size in [16, 64, 256, 1024] {
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context
                        .assume_condition(ConditionTerm::Variable(Variable(167_000 + i)), true);
                }
                context = context.assume_condition(guard.clone(), false);
                let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                    paths(&expression, &context)
                });
                assert_eq!(output.len(), 1);
                assert_eq!(output[0].outcome, CExpressionOutcome::Value(int32(1)));
                assert!(work < 4096, "{size}: {work}");
                samples.push(work);
            }
            assert!(
                samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 128,
                "{samples:?}"
            );
        }
    }
}

#[test]
fn wide_comparison_work_scales_with_explicit_operations() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for operator in OPERATORS {
            let expression = symbolic(operator, ty);
            let context = PureFactContext::new();
            let samples = [2usize, 8, 32, 128].map(|size| {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        assert_eq!(paths(&expression, &context).len(), 2);
                    }
                });
                assert!(work <= 8192 * size, "{size}: {work}");
                work
            });
            for pair in samples.windows(2) {
                assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
            }
        }
    }
}
