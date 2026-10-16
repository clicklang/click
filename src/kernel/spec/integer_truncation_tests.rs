use super::*;

fn truncation(remainder: bool, left: IntegerTerm, right: IntegerTerm) -> SpecIntegerExpression {
    let left = Box::new(SpecIntegerExpression::Term(left));
    let right = Box::new(SpecIntegerExpression::Term(right));
    if remainder {
        SpecIntegerExpression::TruncatingRemainder(left, right)
    } else {
        SpecIntegerExpression::TruncatingQuotient(left, right)
    }
}

#[test]
fn integer_truncation_capture_requires_domain_even_when_result_cancels() {
    let left = IntegerTerm::Variable(Variable(150_091));
    let right = IntegerTerm::Variable(Variable(150_092));
    let nonzero = ConditionTerm::integer_not_equal(right.clone(), IntegerTerm::constant_i64(0));
    let empty = PureFactContext::new();
    let guarded = PureFactContext::new().assume_condition(nonzero, true);
    for remainder in [false, true] {
        let term = truncation(remainder, left.clone(), right.clone());
        let expected = if remainder {
            IntegerTerm::truncating_remainder(left.clone(), right.clone())
        } else {
            IntegerTerm::truncating_quotient(left.clone(), right.clone())
        };
        assert_eq!(
            capture_spec_integer_value(&CState::new(), &term, None, &guarded).unwrap(),
            expected
        );
        for expression in [
            term.clone(),
            SpecIntegerExpression::Multiply(
                Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
                Box::new(term.clone()),
            ),
            SpecIntegerExpression::Subtract(Box::new(term.clone()), Box::new(term)),
        ] {
            assert!(capture_spec_integer_value(&CState::new(), &expression, None, &empty).is_err());
            assert!(
                capture_spec_integer_value(&CState::new(), &expression, None, &guarded).is_ok()
            );
        }
        let zero = truncation(
            remainder,
            IntegerTerm::constant_i64(7),
            IntegerTerm::constant_i64(0),
        );
        assert!(capture_spec_integer_value(&CState::new(), &zero, None, &empty).is_err());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/integer_truncation_tests.rs");
}
