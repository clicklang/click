//! Bound a truncating quotient by an exact Integer multiple of a positive divisor.
//! Reads two named premises only; it infers no native safety or operand ranges.
use super::arithmetic_special::ArithmeticRuleError as Error;
use super::integer_product_bounds::order;
use crate::kernel::{IntegerTerm, Proposition};
use num_traits::{One, Zero};

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
        return Err(Error::InvalidIntegerQuotientBound(node));
    }
    let (left, right) = order(result).ok_or(Error::InvalidOperator(node))?;
    let premise = |index| premises.get(index).ok_or(Error::InvalidPremise(index));
    let (positive, divisor) =
        order(premise(bounds[1])?).ok_or(Error::InvalidIntegerQuotientBound(node))?;
    if positive.as_const().is_none_or(|value| !value.is_one()) {
        return Err(Error::InvalidIntegerQuotientBound(node));
    }
    let (scaled_left, scaled_right) =
        order(premise(bounds[0])?).ok_or(Error::InvalidIntegerQuotientBound(node))?;
    // Either side of the goal may itself be a quotient. Select the rule by
    // the named numerator/divisor identities, never by an opaque bound's kind.
    let (d, bound, product) = match (left.as_ref(), right.as_ref()) {
        (IntegerTerm::TruncatingQuotient(n, d), _) if divisor == d && scaled_left == n => {
            (d, right, scaled_right)
        }
        (_, IntegerTerm::TruncatingQuotient(n, d)) if divisor == d && scaled_right == n => {
            (d, left, scaled_left)
        }
        _ => return Err(Error::InvalidIntegerQuotientBound(node)),
    };
    // Match the multiply constructor's root-local normalization without
    // cloning opaque operands (which can contain large match-arm vectors).
    let matches = if let (Some(b), Some(divisor)) = (bound.as_const(), d.as_const()) {
        let work = (b.bits() as usize + 1).saturating_mul(divisor.bits() as usize + 1);
        if crate::instrumentation::deadline_exceeded_with_work(work) {
            return Err(Error::WorkLimitExceeded);
        }
        product
            .as_const()
            .is_some_and(|value| value == &(b * divisor))
    } else if bound.as_const().is_some_and(Zero::is_zero) || d.as_const().is_some_and(Zero::is_zero)
    {
        product.as_const().is_some_and(Zero::is_zero)
    } else if bound.as_const().is_some_and(One::is_one) {
        product == d
    } else if d.as_const().is_some_and(One::is_one) {
        product == bound
    } else {
        matches!(product.as_ref(), IntegerTerm::Multiply(left, right) if left == bound && right == d)
    };
    if !matches {
        return Err(Error::NodeResultMismatch(node));
    }
    // For d >= 1, truncating division is monotone in the dividend, and
    // truncating_quotient(bound * d, d) == bound for every Integer bound.
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::ConditionTerm;
    use crate::kernel::Variable;
    use num_bigint::BigInt;
    use num_traits::Signed;
    fn c(n: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(n)
    }
    fn v(n: u64) -> IntegerTerm {
        IntegerTerm::var(Variable(n))
    }
    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::condition_is(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    }
    fn case(bound: IntegerTerm, d: IntegerTerm, lower: bool) -> (Vec<Proposition>, Proposition) {
        let n = v(198001);
        let multiple = IntegerTerm::multiply(bound.clone(), d.clone());
        let q = IntegerTerm::truncating_quotient(n.clone(), d.clone());
        let scaled = if lower {
            le(multiple, n)
        } else {
            le(n, multiple)
        };
        let result = if lower { le(bound, q) } else { le(q, bound) };
        (vec![scaled, le(c(1), d)], result)
    }

    #[test]
    fn quotient_bound_signed_wide_oracle_includes_multiple_neighbors() {
        // An independent magnitude/sign oracle, including values far outside int64.
        for bits in [3usize, 31, 63, 95, 127, 255] {
            let magnitude: BigInt = (BigInt::from(1) << bits) - 1;
            for b in [-magnitude.clone(), BigInt::from(0), magnitude] {
                for d in [
                    BigInt::from(1),
                    BigInt::from(3),
                    BigInt::from(2147483647),
                    BigInt::from(1) << 96usize,
                ] {
                    let product = &b * &d;
                    for offset in [
                        -&d - 1,
                        -&d,
                        BigInt::from(-1),
                        BigInt::from(0),
                        BigInt::from(1),
                        d.clone(),
                        &d + 1,
                    ] {
                        let n = &product + offset;
                        let abs_q = n.abs() / &d;
                        let q = if n.is_negative() { -abs_q } else { abs_q };
                        if product <= n {
                            assert!(b <= q);
                        }
                        if n <= product {
                            assert!(q <= b);
                        }
                    }
                }
            }
        }
        // Positivity is necessary: with d=-2, 3*d <= 0 yet 3 <= 0/d is false.
        let (bound, dividend, divisor) = (3i64, 0i64, -2i64);
        assert!(bound * divisor <= dividend && bound > dividend / divisor);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/integer_quotient_bound/tests.rs");
    }
}
