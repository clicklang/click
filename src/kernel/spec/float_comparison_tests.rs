use super::*;
use crate::kernel::VerificationSession;

#[test]
fn float_comparison_lowering_preserves_symbolic_operator_polarity() {
    let _session = VerificationSession::enter();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let left = MachineTerm::Variable(Variable(1008100));
        let right = MachineTerm::Variable(Variable(1008101));
        for operator in [
            ComparisonOperator::Equal,
            ComparisonOperator::NotEqual,
            ComparisonOperator::LessThan,
            ComparisonOperator::LessEqual,
            ComparisonOperator::GreaterThan,
            ComparisonOperator::GreaterEqual,
        ] {
            let condition = FloatCondition::Comparison {
                operator,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            let condition = match format {
                KernelFloatType::Float32 => ConditionTerm::Float32(condition),
                KernelFloatType::Float64 => ConditionTerm::Float64(condition),
            };
            assert_eq!(
                program_value_comparison_proposition(
                    &format.value(left.clone()),
                    operator,
                    &format.value(right.clone())
                ),
                Some(Proposition::ConditionIs(condition, true))
            );
        }
    }
}

#[test]
fn float_inequality_lowering_preserves_ieee_constant_results() {
    let _session = VerificationSession::enter();
    for (format, one, two, negative_zero, nan) in [
        (
            KernelFloatType::Float32,
            0x3f800000,
            0x40000000,
            0x80000000,
            0x7fc00123,
        ),
        (
            KernelFloatType::Float64,
            0x3ff0000000000000,
            0x4000000000000000,
            0x8000000000000000,
            0x7ff8000000000123,
        ),
    ] {
        let value = |bits| {
            format.value(match format {
                KernelFloatType::Float32 => MachineTerm::constant(bits as u32),
                KernelFloatType::Float64 => MachineTerm::uint64_constant(bits),
            })
        };
        for (left, right, unequal) in [
            (one, one, false),
            (one, two, true),
            (0, negative_zero, false),
            (nan, nan, true),
            (nan, one, true),
            (one, nan, true),
        ] {
            for (operator, expected) in [
                (ComparisonOperator::NotEqual, unequal),
                (ComparisonOperator::Equal, !unequal),
            ] {
                assert_eq!(
                    program_value_comparison_proposition(&value(left), operator, &value(right)),
                    Some(Proposition::ConditionIs(
                        ConditionTerm::Constant(expected),
                        true
                    )),
                    "{format:?}: {left:x} {operator:?} {right:x}"
                );
            }
        }
    }
}
