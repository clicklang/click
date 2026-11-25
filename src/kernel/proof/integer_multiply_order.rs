//! Exact multiplication ordering from two selected premises; no ambient search.
use super::arithmetic_special::ArithmeticRuleError as Error;
use crate::kernel::{IntegerTerm, OldConditionTerm, Proposition, SharedIntegerTerm};
use num_traits::{One, Zero};

fn order(p: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match p {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((OldConditionTerm::IntegerLessEqual(a, b), _)) =
                condition_source_0.old_condition() =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

// The constructor folds constants, zero and one. Match those roots without
// rebuilding either opaque operand or traversing unrelated expression state.
fn product(
    p: &SharedIntegerTerm,
    a: &SharedIntegerTerm,
    b: &SharedIntegerTerm,
) -> Result<bool, Error> {
    if let (Some(x), Some(y)) = (a.as_const(), b.as_const()) {
        let work = (x.bits() as usize + 1).saturating_mul(y.bits() as usize + 1);
        if crate::instrumentation::deadline_exceeded_with_work(work) {
            return Err(Error::WorkLimitExceeded);
        }
        Ok(p.as_const().is_some_and(|v| v == &(x * y)))
    } else if a.as_const().is_some_and(Zero::is_zero) || b.as_const().is_some_and(Zero::is_zero) {
        Ok(p.as_const().is_some_and(Zero::is_zero))
    } else if a.as_const().is_some_and(One::is_one) {
        Ok(p == b)
    } else if b.as_const().is_some_and(One::is_one) {
        Ok(p == a)
    } else {
        Ok(
            matches!(p.as_ref(), IntegerTerm::Multiply(x, y) if (x == a && y == b) || (x == b && y == a)),
        )
    }
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 2 {
        return Err(Error::InvalidIntegerMultiplyOrder(node));
    }
    let premise = |i| premises.get(i).ok_or(Error::InvalidPremise(i));
    let (a, b) = order(premise(bounds[0])?).ok_or(Error::InvalidIntegerMultiplyOrder(node))?;
    let (s, t) = order(premise(bounds[1])?).ok_or(Error::InvalidIntegerMultiplyOrder(node))?;
    let (left, right) = order(result).ok_or(Error::InvalidOperator(node))?;
    let follows = if s.as_const().is_some_and(Zero::is_zero) {
        product(left, a, t)? && product(right, b, t)?
    } else if t.as_const().is_some_and(Zero::is_zero) {
        product(left, b, s)? && product(right, a, s)?
    } else {
        return Err(Error::InvalidIntegerMultiplyOrder(node));
    };
    follows.then_some(()).ok_or(Error::NodeResultMismatch(node))
}

#[cfg(test)]
mod tests {

    #[test]
    fn signed_order_and_fee_envelope_oracle() {
        for a in -12i128..=12 {
            for b in a..=12 {
                for factor in -12i128..=12 {
                    assert!(if factor >= 0 {
                        a * factor <= b * factor
                    } else {
                        b * factor <= a * factor
                    });
                }
            }
        }
        for fee in [i64::MIN as i128, -1, 0, 1, i64::MAX as i128] {
            for size in [1i128, 3, 17, i32::MAX as i128] {
                for amount in [0, 1, size - 1, size] {
                    let n = fee * amount;
                    assert!((i64::MIN as i128) * size <= n && n <= (i64::MAX as i128) * size);
                }
            }
        }
    }
}
