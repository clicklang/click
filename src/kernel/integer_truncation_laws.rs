//! Trusted symbolic laws of Integer truncation toward zero. Each constructor
//! retains its divisor/sign premises; native definedness and widths are separate.
use super::prelude::*;

pub(crate) fn integer_truncation_law_requirements(name: &str) -> Option<usize> {
    Some(match name {
        "integer_truncation_identity" => 1,
        "integer_positive_divisor_remainder_lower" | "integer_positive_divisor_remainder_upper" => {
            2
        }
        "integer_nonnegative_dividend_remainder" | "integer_nonpositive_dividend_remainder" => 2,
        _ => return None,
    })
}

pub(crate) fn prove_integer_truncation_law(
    name: &str,
    n: IntegerTerm,
    d: IntegerTerm,
) -> Option<Theorem> {
    integer_truncation_law_requirements(name)?;
    let zero = IntegerTerm::constant_i64(0);
    let one = IntegerTerm::constant_i64(1);
    let condition = |condition| Proposition::ConditionIs(condition, true);
    let nonzero = Proposition::ConditionIs(
        ConditionTerm::IntegerNotEqual(d.clone().into(), zero.clone().into()),
        true,
    );
    let positive = condition(ConditionTerm::IntegerLessThan(
        zero.clone().into(),
        d.clone().into(),
    ));
    let remainder = IntegerTerm::truncating_remainder(n.clone(), d.clone());
    let (premises, conclusion) = match name {
        "integer_truncation_identity" => {
            let quotient = IntegerTerm::truncating_quotient(n.clone(), d.clone());
            let reconstructed = IntegerTerm::add(IntegerTerm::multiply(quotient, d), remainder);
            (
                vec![nonzero],
                condition(ConditionTerm::IntegerEqual(n.into(), reconstructed.into())),
            )
        }
        "integer_positive_divisor_remainder_lower" => (
            vec![nonzero, positive],
            condition(ConditionTerm::IntegerLessEqual(
                IntegerTerm::subtract(one, d).into(),
                remainder.into(),
            )),
        ),
        "integer_positive_divisor_remainder_upper" => (
            vec![nonzero, positive],
            condition(ConditionTerm::IntegerLessEqual(
                remainder.into(),
                IntegerTerm::subtract(d, one).into(),
            )),
        ),
        "integer_nonnegative_dividend_remainder" => (
            vec![
                nonzero,
                condition(ConditionTerm::IntegerLessEqual(
                    zero.clone().into(),
                    n.into(),
                )),
            ],
            condition(ConditionTerm::IntegerLessEqual(
                zero.into(),
                remainder.into(),
            )),
        ),
        "integer_nonpositive_dividend_remainder" => (
            vec![
                nonzero,
                condition(ConditionTerm::IntegerLessEqual(
                    n.into(),
                    zero.clone().into(),
                )),
            ],
            condition(ConditionTerm::IntegerLessEqual(
                remainder.into(),
                zero.into(),
            )),
        ),
        _ => unreachable!("registered truncation law"),
    };
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};

    const N: Variable = Variable(310_001);
    const D: Variable = Variable(310_002);
    const NAMES: [&str; 5] = [
        "integer_truncation_identity",
        "integer_positive_divisor_remainder_lower",
        "integer_positive_divisor_remainder_upper",
        "integer_nonnegative_dividend_remainder",
        "integer_nonpositive_dividend_remainder",
    ];

    // Independent sign/magnitude specification, including negative divisors.
    // This evaluates the emitted symbolic law rather than a constant-folded law.
    fn quotient(n: &BigInt, d: &BigInt) -> BigInt {
        assert!(!d.is_zero());
        let magnitude = n.abs() / d.abs();
        if n.is_negative() != d.is_negative() {
            -magnitude
        } else {
            magnitude
        }
    }
    fn integer(term: &IntegerTerm, n: &BigInt, d: &BigInt) -> BigInt {
        match term {
            IntegerTerm::Variable(v) if *v == N => n.clone(),
            IntegerTerm::Variable(v) if *v == D => d.clone(),
            IntegerTerm::Constant(c) => c.clone(),
            IntegerTerm::Add(a, b) => integer(a, n, d) + integer(b, n, d),
            IntegerTerm::Subtract(a, b) => integer(a, n, d) - integer(b, n, d),
            IntegerTerm::Multiply(a, b) => integer(a, n, d) * integer(b, n, d),
            IntegerTerm::TruncatingQuotient(a, b) => quotient(&integer(a, n, d), &integer(b, n, d)),
            IntegerTerm::TruncatingRemainder(a, b) => {
                let a = integer(a, n, d);
                let b = integer(b, n, d);
                &a - quotient(&a, &b) * b
            }
            _ => panic!("unexpected Integer in truncation law: {term:?}"),
        }
    }
    fn proposition(p: &Proposition, n: &BigInt, d: &BigInt) -> bool {
        match p {
            Proposition::Implies(a, b) => !proposition(a, n, d) || proposition(b, n, d),
            Proposition::ConditionIs(c, truth) => {
                let actual = match c {
                    ConditionTerm::IntegerEqual(a, b) => integer(a, n, d) == integer(b, n, d),
                    ConditionTerm::IntegerNotEqual(a, b) => integer(a, n, d) != integer(b, n, d),
                    ConditionTerm::IntegerLessThan(a, b) => integer(a, n, d) < integer(b, n, d),
                    ConditionTerm::IntegerLessEqual(a, b) => integer(a, n, d) <= integer(b, n, d),
                    _ => panic!("unexpected condition in truncation law: {c:?}"),
                };
                actual == *truth
            }
            _ => panic!("unexpected proposition in truncation law: {p:?}"),
        }
    }
    #[test]
    fn integer_truncation_laws_match_signed_and_arbitrary_width_oracles() {
        let mut samples: Vec<BigInt> = (-12..=12).map(BigInt::from).collect();
        for width in [31, 63, 127, 255] {
            let power = BigInt::from(1) << width;
            for delta in [-1, 0, 1] {
                let value: BigInt = &power + delta;
                samples.extend([value.clone(), -value]);
            }
        }
        for name in NAMES {
            let law = prove_integer_truncation_law(name, IntegerTerm::var(N), IntegerTerm::var(D))
                .unwrap();
            for n in &samples {
                for d in &samples {
                    assert!(proposition(law.proposition(), n, d), "{name}: n={n}, d={d}");
                }
            }
            // Guard polarity/count is part of the trusted theorem boundary.
            let mut body = law.proposition();
            let mut count = 0;
            while let Proposition::Implies(_, next) = body {
                count += 1;
                body = next;
            }
            assert_eq!(Some(count), integer_truncation_law_requirements(name));
        }
        assert!(
            prove_integer_truncation_law("unknown", IntegerTerm::var(N), IntegerTerm::var(D))
                .is_none()
        );
    }
}
