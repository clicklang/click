//! Exclude one constant from one explicit non-strict Integer bound.
use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{ConditionTerm, Proposition};

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    let invalid = || Error::InvalidIntegerBoundExclusion(node);
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 1 {
        return Err(invalid());
    }
    let (a, b) = match result {
        Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(a, b), true)
        | Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), false) => (a, b),
        _ => return Err(invalid()),
    };
    let (term, excluded) = if let Some(c) = a.as_const() {
        (b, c)
    } else if let Some(c) = b.as_const() {
        (a, c)
    } else {
        return Err(invalid());
    };
    let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(lo, hi), true) = premises
        .get(bounds[0])
        .ok_or(Error::InvalidPremise(bounds[0]))?
    else {
        return Err(invalid());
    };
    let (endpoint, lower) = if hi == term {
        (lo.as_const(), true)
    } else if lo == term {
        (hi.as_const(), false)
    } else {
        return Err(invalid());
    };
    let endpoint = endpoint.ok_or_else(invalid)?;
    let work = usize::try_from(endpoint.bits())
        .unwrap_or(usize::MAX)
        .saturating_add(usize::try_from(excluded.bits()).unwrap_or(usize::MAX))
        .saturating_add(16);
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(Error::WorkLimitExceeded);
    }
    if if lower {
        excluded < endpoint
    } else {
        excluded > endpoint
    } {
        Ok(())
    } else {
        Err(invalid())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        IntegerTerm, Variable,
        proof::arithmetic_special::{SpecialArithmeticCertificate, SpecialArithmeticNode},
    };
    use num_bigint::BigInt;
    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    }
    fn ne(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(a.into(), b.into()), true)
    }
    #[test]
    fn integer_bound_exclusion_signed_oracle_and_hostile_shapes() {
        let x = IntegerTerm::var(Variable(182001));
        let y = IntegerTerm::var(Variable(182002));
        for endpoint in -4i64..=4 {
            for excluded in -5i64..=5 {
                for lower in [false, true] {
                    let p = if lower {
                        le(IntegerTerm::constant(endpoint.into()), x.clone())
                    } else {
                        le(x.clone(), IntegerTerm::constant(endpoint.into()))
                    };
                    for reversed in [false, true] {
                        let goal = if reversed {
                            ne(IntegerTerm::constant(excluded.into()), x.clone())
                        } else {
                            ne(x.clone(), IntegerTerm::constant(excluded.into()))
                        };
                        let valid = if lower {
                            excluded < endpoint
                        } else {
                            excluded > endpoint
                        };
                        assert_eq!(
                            check(0, &[0], std::slice::from_ref(&p), &goal).is_ok(),
                            valid
                        );
                        if valid {
                            for value in -10..=10 {
                                if if lower {
                                    value >= endpoint
                                } else {
                                    value <= endpoint
                                } {
                                    assert_ne!(value, excluded);
                                }
                            }
                            let cert = SpecialArithmeticCertificate {
                                nodes: vec![SpecialArithmeticNode::IntegerBoundExclusion {
                                    bounds: vec![0],
                                    result: goal.clone(),
                                }],
                                conclusion: 0,
                            };
                            cert.check(&goal, std::slice::from_ref(&p)).unwrap();
                            let wrong_goal = ne(x.clone(), x.clone());
                            assert!(cert.check(&wrong_goal, std::slice::from_ref(&p)).is_err());
                            let mut false_goal = goal.clone();
                            if let Proposition::ConditionIs(_, truth) = &mut false_goal {
                                *truth = false;
                            }
                            assert!(cert.check(&false_goal, std::slice::from_ref(&p)).is_err());
                            let forged = SpecialArithmeticCertificate {
                                conclusion: 1,
                                ..cert
                            };
                            assert!(forged.check(&goal, std::slice::from_ref(&p)).is_err());
                        }
                        for refs in [vec![], vec![1], vec![0, 0]] {
                            assert!(check(0, &refs, std::slice::from_ref(&p), &goal).is_err());
                        }
                    }
                }
            }
        }
        let p = le(IntegerTerm::constant(1.into()), x.clone());
        let goal = ne(x.clone(), IntegerTerm::constant(0.into()));
        let false_equal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(x.clone().into(), IntegerTerm::constant(0.into()).into()),
            false,
        );
        assert!(check(0, &[0], std::slice::from_ref(&p), &false_equal).is_ok());
        for wrong in [
            le(x.clone(), IntegerTerm::constant(0.into())),
            ne(y, IntegerTerm::constant(0.into())),
            ne(x.clone(), x.clone()),
        ] {
            assert!(check(0, &[0], std::slice::from_ref(&p), &wrong).is_err());
        }
        let mut opposite = goal.clone();
        if let Proposition::ConditionIs(_, value) = &mut opposite {
            *value = false;
        }
        assert!(check(0, &[0], std::slice::from_ref(&p), &opposite).is_err());
        let mut false_bound = p.clone();
        if let Proposition::ConditionIs(_, value) = &mut false_bound {
            *value = false;
        }
        assert!(check(0, &[0], &[false_bound], &goal).is_err());
        // A nonlinear operand remains a shared node rather than an affine atom.
        let term = IntegerTerm::truncating_quotient(x.clone(), x);
        let p = le(IntegerTerm::constant(1.into()), term.clone());
        assert!(check(0, &[0], &[p], &ne(term, IntegerTerm::constant(0.into()))).is_ok());
    }
    #[test]
    fn integer_bound_exclusion_work_scales_with_nodes_and_magnitude_not_unused_facts() {
        let x = IntegerTerm::var(Variable(182001));
        let goal = ne(x.clone(), IntegerTerm::constant(0.into()));
        let mut p = vec![le(IntegerTerm::constant(1.into()), x.clone())];
        let mut baseline = None;
        for size in [4usize, 16, 64, 256] {
            while p.len() < size {
                p.push(le(x.clone(), x.clone()));
            }
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| check(0, &[0], &p, &goal));
            checked.unwrap();
            assert_eq!(*baseline.get_or_insert(work), work);
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerBoundExclusion {
                        bounds: vec![0],
                        result: goal.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &p));
            checked.unwrap();
            assert_eq!(work, size * baseline.unwrap() + 1);
        }
        let mut previous = 0;
        for bits in [64usize, 128, 256, 512, 1024] {
            let endpoint = BigInt::from(1) << bits;
            let p = [le(IntegerTerm::constant(endpoint), x.clone())];
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| check(0, &[0], &p, &goal));
            checked.unwrap();
            assert!(work > previous);
            previous = work;
            crate::instrumentation::with_run_work_limit(work - 1, || {
                assert_eq!(check(0, &[0], &p, &goal), Err(Error::WorkLimitExceeded))
            });
            crate::instrumentation::with_run_work_limit(work, || {
                check(0, &[0], &p, &goal).unwrap()
            });
        }
    }
}
