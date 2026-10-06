//! Truncation agrees with floor on nonnegative numerators: adding d*k shifts
//! the quotient by k when d is a positive constant and both x and k are >= 0.
use super::arithmetic_special::SpecialArithmeticCheckError as Error;
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
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = result else {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        Variable,
        proof::arithmetic_special::{SpecialArithmeticCertificate, SpecialArithmeticNode},
    };
    fn c(n: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(n)
    }
    fn x() -> IntegerTerm {
        IntegerTerm::var(Variable(186_001))
    }
    fn k() -> IntegerTerm {
        IntegerTerm::var(Variable(186_002))
    }
    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    }
    fn goal(d: i64, increment: IntegerTerm) -> Proposition {
        let a = IntegerTerm::truncating_quotient(
            IntegerTerm::add(x(), IntegerTerm::multiply(c(d), k())),
            c(d),
        );
        let b = IntegerTerm::add(IntegerTerm::truncating_quotient(x(), c(d)), increment);
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }
    #[test]
    fn quotient_shift_checks_divisor_sign_guards_and_exact_operands() {
        let premises = vec![le(c(0), x()), le(c(0), k())];
        for d in [2, 3, 17, 65521] {
            let result = goal(d, k());
            assert_eq!(check(0, &[0, 1], &premises, &result), Ok(()));
            assert!(check(0, &[1, 0], &premises, &result).is_err());
            assert!(check(0, &[0], &premises, &result).is_err());
            assert!(check(0, &[0, 2], &premises, &result).is_err());
            assert!(check(0, &[0, 1], &premises, &goal(d, IntegerTerm::add(k(), c(1)))).is_err());
            for which in [0, 1] {
                let mut false_premises = premises.clone();
                if let Proposition::ConditionIs(_, truth) = &mut false_premises[which] {
                    *truth = false;
                }
                assert!(check(0, &[0, 1], &false_premises, &result).is_err());
                false_premises[which] = if which == 0 {
                    le(c(-1), x())
                } else {
                    le(c(-1), k())
                };
                assert!(check(0, &[0, 1], &false_premises, &result).is_err());
            }
            let mut false_result = result.clone();
            if let Proposition::ConditionIs(_, truth) = &mut false_result {
                *truth = false;
            }
            assert!(check(0, &[0, 1], &premises, &false_result).is_err());
            let cert = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::IntegerQuotientShift {
                    bounds: vec![0, 1],
                    result: result.clone(),
                }],
                conclusion: 0,
            };
            cert.check(&result, &premises).unwrap();
            assert!(cert.check(&false_result, &premises).is_err());
        }
        for d in [-17, -2, 0] {
            assert!(check(0, &[0, 1], &premises, &goal(d, k())).is_err());
        }
        // Exhaustive concrete oracle includes odd numerators; parity is unnecessary.
        for d in 1..=17i64 {
            for n in 0..=33 {
                for shift in 0..=17 {
                    assert_eq!((n + d * shift) / d, n / d + shift);
                }
            }
        }
        // Negative inputs can cross zero, where truncation ceases to be translation invariant.
        let trunc = |n: i64, d: i64| n / d;
        assert_ne!(trunc(-1 + 2, 2), trunc(-1, 2) + 1);
    }
    #[test]
    fn quotient_shift_work_is_local_and_linear_in_certificate_nodes() {
        let result = goal(2, k());
        let mut premises = vec![le(c(0), x()), le(c(0), k())];
        let (_, single_work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1], &premises, &result)
        });
        for size in [4, 16, 64, 256] {
            premises.resize(size, le(c(0), c(1)));
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[0, 1], &premises, &result)
            });
            checked.unwrap();
            assert_eq!(work, single_work);
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerQuotientShift {
                        bounds: vec![0, 1],
                        result: result.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                cert.check(&result, &premises)
            });
            checked.unwrap();
            assert_eq!(work, single_work * size + 1);
        }
    }
}
