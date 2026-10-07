//! Exact multiplication ordering from two selected premises; no ambient search.
use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};
use num_traits::{One, Zero};

fn order(p: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match p {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => Some((a, b)),
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
    use super::*;
    use crate::kernel::{
        Variable,
        proof::arithmetic_special::{SpecialArithmeticCertificate, SpecialArithmeticNode},
    };
    fn c(n: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(n)
    }
    fn v(n: u64) -> IntegerTerm {
        IntegerTerm::var(Variable(n))
    }
    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    }
    fn p(a: &IntegerTerm, b: &IntegerTerm) -> IntegerTerm {
        IntegerTerm::multiply(a.clone(), b.clone())
    }
    #[test]
    fn exact_sign_order_products_and_premise_selection() {
        for reverse in [false, true] {
            for factor in [c(0), c(1), c(-1), c(17), v(920003)] {
                for (a, b) in [(v(920001), v(920002)), (c(-7), c(9)), (c(0), c(1))] {
                    let sign = if reverse {
                        le(factor.clone(), c(0))
                    } else {
                        le(c(0), factor.clone())
                    };
                    // Inconsistent premises remain logically sound: this is a conditional rule.
                    let premises = vec![le(a.clone(), b.clone()), sign];
                    for swap in [false, true] {
                        let prod = |x| if swap { p(&factor, x) } else { p(x, &factor) };
                        let result = if reverse {
                            le(prod(&b), prod(&a))
                        } else {
                            le(prod(&a), prod(&b))
                        };
                        check(0, &[0, 1], &premises, &result).unwrap();
                        let cert = SpecialArithmeticCertificate {
                            nodes: vec![SpecialArithmeticNode::IntegerMultiplyOrder {
                                bounds: vec![0, 1],
                                result: result.clone(),
                            }],
                            conclusion: 0,
                        };
                        cert.check(&result, &premises).unwrap();
                        for indices in [vec![], vec![0], vec![0, 2], vec![0, 1, 0]] {
                            assert!(check(0, &indices, &premises, &result).is_err());
                        }
                        for i in [0, 1] {
                            let mut bad = premises.clone();
                            if let Proposition::ConditionIs(_, truth) = &mut bad[i] {
                                *truth = false;
                            }
                            assert!(check(0, &[0, 1], &bad, &result).is_err());
                        }
                        assert!(check(0, &[0, 1], &premises, &le(v(920004), v(920005))).is_err());
                    }
                }
            }
        }
        let a = v(920001);
        let b = v(920002);
        let factor = v(920003);
        let inputs = vec![le(a.clone(), b.clone()), le(c(0), factor.clone())];
        assert!(check(0, &[1, 0], &inputs, &le(p(&a, &factor), p(&b, &factor))).is_err());
        for goal in [
            le(p(&b, &factor), p(&a, &factor)),
            le(p(&a, &v(920004)), p(&b, &factor)),
            le(p(&a, &factor), p(&b, &v(920004))),
        ] {
            assert!(check(0, &[0, 1], &inputs, &goal).is_err());
        }
        assert!(
            check(
                0,
                &[0, 1],
                &[inputs[0].clone(), le(c(1), factor.clone())],
                &le(p(&a, &factor), p(&b, &factor))
            )
            .is_err()
        );
    }
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
    #[test]
    fn selected_premises_and_steps_scale_without_ambient_scans() {
        let a = v(920001);
        let b = v(920002);
        let factor = v(920003);
        let goal = le(p(&a, &factor), p(&b, &factor));
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let mut premises = vec![le(a.clone(), b.clone()), le(c(0), factor.clone())];
            premises.extend((0..size).map(|i| le(v(930000 + i as u64), c(i as i64))));
            let cert = SpecialArithmeticCertificate {
                nodes: (0..size)
                    .map(|_| SpecialArithmeticNode::IntegerMultiplyOrder {
                        bounds: vec![0, 1],
                        result: goal.clone(),
                    })
                    .collect(),
                conclusion: size - 1,
            };
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{samples:?}");
        }
    }
}
