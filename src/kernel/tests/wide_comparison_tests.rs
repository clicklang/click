use super::*;
use num_bigint::BigInt;

const LEFT: Variable = Variable(166_001);
const RIGHT: Variable = Variable(166_002);
const OPERATORS: [ComparisonOperator; 6] = [
    ComparisonOperator::Equal,
    ComparisonOperator::NotEqual,
    ComparisonOperator::LessThan,
    ComparisonOperator::LessEqual,
    ComparisonOperator::GreaterThan,
    ComparisonOperator::GreaterEqual,
];

fn compare(
    operator: ComparisonOperator,
    a: ProgramExpression,
    b: ProgramExpression,
) -> ProgramExpression {
    match operator {
        ComparisonOperator::Equal => crate::kernel::program_expression::equal(a, b),
        ComparisonOperator::NotEqual => crate::kernel::program_expression::not_equal(a, b),
        ComparisonOperator::LessThan => crate::kernel::program_expression::less_than(a, b),
        ComparisonOperator::LessEqual => crate::kernel::program_expression::less_equal(a, b),
        ComparisonOperator::GreaterThan => crate::kernel::program_expression::greater_than(a, b),
        ComparisonOperator::GreaterEqual => crate::kernel::program_expression::greater_equal(a, b),
    }
}

fn condition(operator: ComparisonOperator, ty: MachineIntegerType) -> ConditionTerm {
    let a = IntegerTerm::from_machine(ty, MachineTerm::Variable(LEFT)).unwrap();
    let b = IntegerTerm::from_machine(ty, MachineTerm::Variable(RIGHT)).unwrap();
    match operator {
        ComparisonOperator::Equal => ConditionTerm::integer_equal(a, b),
        ComparisonOperator::NotEqual => ConditionTerm::integer_not_equal(a, b),
        ComparisonOperator::LessThan => ConditionTerm::integer_less_than(a, b),
        ComparisonOperator::LessEqual => ConditionTerm::integer_less_equal(a, b),
        ComparisonOperator::GreaterThan => ConditionTerm::integer_greater_than(a, b),
        ComparisonOperator::GreaterEqual => ConditionTerm::integer_greater_equal(a, b),
    }
}

fn complement(operator: ComparisonOperator) -> ComparisonOperator {
    match operator {
        ComparisonOperator::Equal => ComparisonOperator::NotEqual,
        ComparisonOperator::NotEqual => ComparisonOperator::Equal,
        ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
        ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
        ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
    }
}

fn symbolic(operator: ComparisonOperator, ty: MachineIntegerType) -> ProgramExpression {
    let value = |variable| {
        ProgramExpression::Value(match ty {
            MachineIntegerType::Int128 => ProgramValue::Int128(MachineTerm::Variable(variable)),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(MachineTerm::Variable(variable)),
            _ => unreachable!(),
        })
    };
    compare(operator, value(LEFT), value(RIGHT))
}

fn paths(expression: &ProgramExpression, context: &PureFactContext) -> Vec<ExpressionPath> {
    evaluate_program_expression_paths(
        &ExecutionState::new(),
        expression,
        context,
        &mut ExecutionBudget::for_program_expression(expression),
    )
    .unwrap()
}

fn outcome(expression: ProgramExpression) -> ExpressionOutcome {
    let theorem = prove_program_expression_evaluation(ExecutionState::new(), expression).unwrap();
    let Proposition::ProgramExpressionEvaluates { outcome, .. } = theorem.proposition() else {
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
            ProgramExpression::Value(
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
                        ComparisonOperator::Equal => a == b,
                        ComparisonOperator::NotEqual => a != b,
                        ComparisonOperator::LessThan => a < b,
                        ComparisonOperator::LessEqual => a <= b,
                        ComparisonOperator::GreaterThan => a > b,
                        ComparisonOperator::GreaterEqual => a >= b,
                    };
                    assert_eq!(
                        outcome(compare(operator, literal(a), literal(b))),
                        ExpressionOutcome::Value(int32(u32::from(expected))),
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
                    ExpressionOutcome::Value(int32(u32::from(truth)))
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
                    ExpressionOutcome::Value(int32(u32::from(truth)))
                );
            }
            assert!(
                prove_program_expression_evaluation(ExecutionState::new(), expression).is_none()
            );
        }
    }
}

#[test]
fn wide_comparison_requires_explicit_promotions_and_preserves_operand_failures() {
    for operator in OPERATORS {
        for (a, b) in [
            (
                crate::kernel::program_expression::int128_literal(7),
                crate::kernel::program_expression::uint128_literal(3),
            ),
            (
                crate::kernel::program_expression::int128_literal(7),
                crate::kernel::program_expression::int64_literal(3),
            ),
            (
                crate::kernel::program_expression::uint128_literal(7),
                crate::kernel::program_expression::int32_literal(3),
            ),
            (
                crate::kernel::program_expression::uint128_literal(7),
                program_void_value(),
            ),
        ] {
            assert_eq!(
                outcome(compare(operator, a, b)),
                ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
            );
        }
        let converted = crate::kernel::program_expression::integer_cast_modulo(
            crate::kernel::program_expression::int64_literal(-1),
            ProgramType::UInt128,
        );
        assert_eq!(
            outcome(compare(
                ComparisonOperator::GreaterThan,
                converted,
                crate::kernel::program_expression::uint128_literal(7)
            )),
            ExpressionOutcome::Value(int32(1))
        );
        for on_left in [false, true] {
            for (bad, expected) in [
                (
                    crate::kernel::program_expression::divide(
                        crate::kernel::program_expression::int128_literal(1),
                        crate::kernel::program_expression::int128_literal(0),
                    ),
                    UndefinedBehavior::DivisionByZero,
                ),
                (
                    crate::kernel::program_expression::remainder(
                        crate::kernel::program_expression::int128_literal(i128::MIN),
                        crate::kernel::program_expression::int128_literal(-1),
                    ),
                    UndefinedBehavior::SignedOverflow,
                ),
            ] {
                let good = crate::kernel::program_expression::int128_literal(0);
                let (a, b) = if on_left { (bad, good) } else { (good, bad) };
                assert_eq!(
                    outcome(compare(operator, a, b)),
                    ExpressionOutcome::UndefinedBehavior(expected)
                );
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/wide_comparison_tests.rs");
}
