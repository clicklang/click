//! Truncation agrees with floor on nonnegative numerators: adding d*k shifts
//! the quotient by k when d is a positive constant and both x and k are >= 0.
use super::arithmetic_special::ArithmeticRuleError as Error;
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};
use num_traits::{Signed, Zero};

fn nonnegative(p: &Proposition, value: &SharedIntegerTerm) -> bool {
    matches!(p, Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(zero, x), true)
        if zero.as_const().is_some_and(|c| c.is_zero()) && x == value)
}
pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    if crate::instrumentation::deadline_exceeded_with_work(12) {
        return Err(Error::WorkLimitExceeded);
    }
    let invalid = || Error::InvalidIntegerQuotientShift(node);
    if bounds.len() != 2 {
        return Err(invalid());
    }
    let Some((ConditionTerm::IntegerEqual(left, right), true)) = result.condition_native() else {
        return Err(invalid());
    };
    let IntegerTerm::TruncatingQuotient(sum, d) = left.as_ref() else {
        return Err(invalid());
    };
    let Some(divisor) = d.as_const() else {
        return Err(invalid());
    };
    if crate::instrumentation::deadline_exceeded_with_work(divisor.bits() as usize + 1) {
        return Err(Error::WorkLimitExceeded);
    }
    if !divisor.is_positive() {
        return Err(invalid());
    }
    let IntegerTerm::Add(x, multiple) = sum.as_ref() else {
        return Err(invalid());
    };
    let IntegerTerm::Multiply(factor, k) = multiple.as_ref() else {
        return Err(invalid());
    };
    if factor != d {
        return Err(invalid());
    }
    let IntegerTerm::Add(quotient, increment) = right.as_ref() else {
        return Err(invalid());
    };
    let IntegerTerm::TruncatingQuotient(numerator, denominator) = quotient.as_ref() else {
        return Err(invalid());
    };
    if numerator != x || denominator != d || increment != k {
        return Err(invalid());
    }
    for (index, value) in bounds.iter().zip([x, k]) {
        let premise = premises.get(*index).ok_or(Error::InvalidPremise(*index))?;
        if !nonnegative(premise, value) {
            return Err(invalid());
        }
    }
    Ok(())
}
