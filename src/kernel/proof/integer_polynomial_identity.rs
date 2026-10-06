//! Bounded, explicit ring equality checking over mathematical Integer terms.
//! Non-ring roots stay opaque. No premises, machine algebra, or ambient search.
use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

type Polynomial = BTreeMap<Vec<u64>, BigInt>;
const MAX_NODES: usize = 256;
const MAX_MONOMIALS: usize = 256;
const MAX_DEGREE: usize = 16;
const MAX_BITS: u64 = 4096;

fn charge(work: usize) -> Result<(), Error> {
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        Err(Error::WorkLimitExceeded)
    } else {
        Ok(())
    }
}
fn bits(value: &BigInt) -> usize {
    value.bits() as usize + 1
}
fn insert(poly: &mut Polynomial, monomial: Vec<u64>, coefficient: BigInt) -> Result<(), Error> {
    // A bounded key comparison and tree lookup, plus magnitude-dependent add.
    charge(256usize.saturating_add(bits(&coefficient)))?;
    let sum = if let Some(old) = poly.get(&monomial) {
        charge(bits(old).saturating_add(bits(&coefficient)))?;
        old + coefficient
    } else {
        coefficient
    };
    if sum.bits() > MAX_BITS {
        return Err(Error::IntegerPolynomialLimitExceeded);
    }
    if sum.is_zero() {
        poly.remove(&monomial);
    } else {
        poly.insert(monomial, sum);
    }
    if poly.len() > MAX_MONOMIALS {
        return Err(Error::IntegerPolynomialLimitExceeded);
    }
    Ok(())
}
fn combine(
    a: &Polynomial,
    b: &Polynomial,
    multiply: bool,
    subtract: bool,
) -> Result<Polynomial, Error> {
    let mut out = Polynomial::new();
    if multiply {
        for (ak, av) in a {
            for (bk, bv) in b {
                charge(256usize.saturating_add(bits(av).saturating_mul(bits(bv))))?;
                if ak.len().saturating_add(bk.len()) > MAX_DEGREE {
                    return Err(Error::IntegerPolynomialLimitExceeded);
                }
                let mut key = ak.clone();
                key.extend(bk);
                key.sort_unstable();
                insert(&mut out, key, av * bv)?;
            }
        }
    } else {
        for (key, value) in a {
            charge(bits(value).saturating_add(key.len()))?;
            insert(&mut out, key.clone(), value.clone())?;
        }
        for (key, value) in b {
            charge(bits(value).saturating_add(key.len()))?;
            insert(
                &mut out,
                key.clone(),
                if subtract { -value } else { value.clone() },
            )?;
        }
    }
    Ok(out)
}

fn expand(
    root: &SharedIntegerTerm,
    memo: &mut BTreeMap<u64, Polynomial>,
    seen: &mut BTreeSet<u64>,
) -> Result<(), Error> {
    let mut stack = vec![(root.clone(), false)];
    while let Some((term, ready)) = stack.pop() {
        // Includes bounded memo lookup cost; DAG children are visited once.
        charge(16)?;
        if memo.contains_key(&term.id()) {
            continue;
        }
        if !ready {
            seen.insert(term.id());
            if seen.len() > MAX_NODES {
                return Err(Error::IntegerPolynomialLimitExceeded);
            }
            stack.push((term.clone(), true));
            match term.as_ref() {
                IntegerTerm::Negate(a) => stack.push((a.clone(), false)),
                IntegerTerm::Add(a, b)
                | IntegerTerm::Subtract(a, b)
                | IntegerTerm::Multiply(a, b) => {
                    stack.push((b.clone(), false));
                    stack.push((a.clone(), false));
                }
                _ => {}
            }
            continue;
        }
        let poly = match term.as_ref() {
            IntegerTerm::Constant(value) => {
                charge(bits(value))?;
                if value.bits() > MAX_BITS {
                    return Err(Error::IntegerPolynomialLimitExceeded);
                }
                let mut poly = Polynomial::new();
                insert(&mut poly, vec![], value.clone())?;
                poly
            }
            IntegerTerm::Negate(a) => combine(&Polynomial::new(), &memo[&a.id()], false, true)?,
            IntegerTerm::Add(a, b) => combine(&memo[&a.id()], &memo[&b.id()], false, false)?,
            IntegerTerm::Subtract(a, b) => combine(&memo[&a.id()], &memo[&b.id()], false, true)?,
            IntegerTerm::Multiply(a, b) => combine(&memo[&a.id()], &memo[&b.id()], true, false)?,
            _ => {
                let mut poly = Polynomial::new();
                insert(&mut poly, vec![term.id()], BigInt::one())?;
                poly
            }
        };
        memo.insert(term.id(), poly);
    }
    Ok(())
}

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    _: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    charge(1)?;
    if !bounds.is_empty() {
        return Err(Error::InvalidIntegerPolynomialIdentity(node));
    }
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = result else {
        return Err(Error::InvalidIntegerPolynomialIdentity(node));
    };
    let mut memo = BTreeMap::new();
    let mut seen = BTreeSet::new();
    expand(a, &mut memo, &mut seen)?;
    expand(b, &mut memo, &mut seen)?;
    let left = &memo[&a.id()];
    let right = &memo[&b.id()];
    for (key, value) in left.iter().chain(right.iter()) {
        charge(
            256usize
                .saturating_add(key.len())
                .saturating_add(bits(value)),
        )?;
    }
    if left == right {
        Ok(())
    } else {
        Err(Error::InvalidIntegerPolynomialIdentity(node))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        Variable,
        proof::arithmetic_special::{SpecialArithmeticCertificate, SpecialArithmeticNode},
    };
    fn x() -> IntegerTerm {
        IntegerTerm::var(Variable(184_001))
    }
    fn c(n: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(n)
    }
    fn eq(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }
    fn successor() -> Proposition {
        eq(
            IntegerTerm::multiply(IntegerTerm::add(x(), c(1)), IntegerTerm::add(x(), c(2))),
            IntegerTerm::add(
                IntegerTerm::multiply(x(), IntegerTerm::add(x(), c(1))),
                IntegerTerm::multiply(c(2), IntegerTerm::add(x(), c(1))),
            ),
        )
    }
    #[test]
    fn polynomial_identity_checks_ring_laws_and_rejects_forged_results() {
        let goal = successor();
        assert_eq!(check(0, &[], &[], &goal), Ok(()));
        for delta in [-2, -1, 1, 2] {
            assert!(
                check(
                    0,
                    &[],
                    &[],
                    &eq(
                        IntegerTerm::multiply(x(), x()),
                        IntegerTerm::add(IntegerTerm::multiply(x(), x()), c(delta))
                    )
                )
                .is_err()
            );
        }
        let mut false_goal = goal.clone();
        if let Proposition::ConditionIs(_, truth) = &mut false_goal {
            *truth = false;
        }
        assert!(check(0, &[], &[], &false_goal).is_err());
        assert!(check(0, &[0], std::slice::from_ref(&goal), &goal).is_err());
        // Negative coefficients, cancellation, commutativity, and big coefficients.
        for coefficient in [-1000, -1, 0, 1, 1000] {
            let y = IntegerTerm::var(Variable(184_002));
            let a = IntegerTerm::multiply(c(coefficient), IntegerTerm::subtract(x(), y.clone()));
            let b = IntegerTerm::subtract(
                IntegerTerm::multiply(x(), c(coefficient)),
                IntegerTerm::multiply(c(coefficient), y),
            );
            assert_eq!(check(0, &[], &[], &eq(a, b)), Ok(()));
        }
        let big = IntegerTerm::constant(BigInt::one() << 200usize);
        assert_eq!(
            check(
                0,
                &[],
                &[],
                &eq(
                    IntegerTerm::multiply(big.clone(), x()),
                    IntegerTerm::multiply(x(), big)
                )
            ),
            Ok(())
        );
        // A quotient is an opaque atom: division is not distributive over addition.
        assert!(
            check(
                0,
                &[],
                &[],
                &eq(
                    IntegerTerm::truncating_quotient(IntegerTerm::add(x(), c(1)), c(2)),
                    IntegerTerm::add(IntegerTerm::truncating_quotient(x(), c(2)), c(1))
                )
            )
            .is_err()
        );
        let cert = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerPolynomialIdentity {
                bounds: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        cert.check(&goal, &[]).unwrap();
        assert!(cert.check(&false_goal, &[]).is_err());
    }
    #[test]
    fn polynomial_identity_is_bounded_and_independent_of_unused_premises() {
        let goal = successor();
        let (_, single_work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[], &[], &goal));
        for size in [1, 4, 16, 64] {
            let premises = vec![goal.clone(); size];
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[], &premises, &goal)
            });
            result.unwrap();
            assert_eq!(work, single_work);
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerPolynomialIdentity {
                        bounds: vec![],
                        result: goal.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&goal, &premises));
            result.unwrap();
            assert_eq!(work, single_work * size + 1);
        }
        let mut power = x();
        for _ in 1..17 {
            power = IntegerTerm::multiply(power, x());
        }
        assert_eq!(
            check(0, &[], &[], &eq(power.clone(), power)),
            Err(Error::IntegerPolynomialLimitExceeded)
        );
        let huge = IntegerTerm::constant(BigInt::one() << 4097usize);
        assert_eq!(
            check(0, &[], &[], &eq(huge.clone(), huge)),
            Err(Error::IntegerPolynomialLimitExceeded)
        );
        let mut many = x();
        for index in 0..300 {
            many = IntegerTerm::add(many, IntegerTerm::var(Variable(185_000 + index)));
        }
        assert_eq!(
            check(0, &[], &[], &eq(many.clone(), many)),
            Err(Error::IntegerPolynomialLimitExceeded)
        );
        // Shared squaring cannot expand into an unbounded polynomial.
        let mut exponential = IntegerTerm::add(x(), c(1));
        for _ in 0..10 {
            exponential = IntegerTerm::multiply(exponential.clone(), exponential);
        }
        assert_eq!(
            check(0, &[], &[], &eq(exponential.clone(), exponential)),
            Err(Error::IntegerPolynomialLimitExceeded)
        );
    }
    #[test]
    fn polynomial_identity_work_scales_with_a_fixed_width_ring_dag() {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let mut sum = x();
            for _ in 0..size {
                sum = IntegerTerm::add(sum, c(1));
            }
            let result = eq(sum, IntegerTerm::add(x(), c(size)));
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| check(0, &[], &[], &result));
            checked.unwrap();
            costs.push(work);
            assert_eq!(
                crate::instrumentation::with_run_work_limit(work, || check(0, &[], &[], &result)),
                Ok(())
            );
            assert_eq!(
                crate::instrumentation::with_run_work_limit(work - 1, || check(
                    0,
                    &[],
                    &[],
                    &result
                )),
                Err(Error::WorkLimitExceeded)
            );
        }
        assert!(
            costs.windows(2).all(|pair| pair[1] <= 3 * pair[0]),
            "{costs:?}"
        );
    }
    #[test]
    fn polynomial_identity_counts_distinct_nodes_not_pending_dag_edges() {
        let mut shared = x();
        for _ in 0..128 {
            shared = IntegerTerm::add(shared.clone(), shared);
        }
        assert_eq!(check(0, &[], &[], &eq(shared.clone(), shared)), Ok(()));
        let mut exact = x();
        for _ in 0..254 {
            exact = IntegerTerm::add(exact, c(1));
        }
        assert_eq!(
            check(0, &[], &[], &eq(exact.clone(), exact.clone())),
            Ok(())
        );
        let too_many = IntegerTerm::add(exact, c(1));
        assert_eq!(
            check(0, &[], &[], &eq(too_many.clone(), too_many)),
            Err(Error::IntegerPolynomialLimitExceeded)
        );
    }
}
