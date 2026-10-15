// Scaling tests of `src/kernel/proof/integer_relation_transport.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_relation_transport_checks_equality_direction_and_exact_operands() {
    let a = IntegerTerm::var(Variable(181_001));
    let b = IntegerTerm::var(Variable(181_002));
    let c = IntegerTerm::var(Variable(181_003));
    let equality = |x: IntegerTerm, y: IntegerTerm| {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(x.into(), y.into()), true)
    };
    for swapped in [false, true] {
        let eq = if swapped {
            equality(b.clone(), a.clone())
        } else {
            equality(a.clone(), b.clone())
        };
        for lower in [false, true] {
            let bound = if lower {
                le(c.clone(), a.clone())
            } else {
                le(a.clone(), c.clone())
            };
            let result = if lower {
                le(c.clone(), b.clone())
            } else {
                le(b.clone(), c.clone())
            };
            let p = vec![eq.clone(), bound];
            assert_eq!(check(0, &[0, 1], &p, &result), Ok(()));
            assert!(check(0, &[1, 0], &p, &result).is_err());
            assert!(check(0, &[0], &p, &result).is_err());
            assert!(check(0, &[0, 2], &p, &result).is_err());
            assert!(check(0, &[0, 1], &p, &le(b.clone(), b.clone())).is_err());
            let mut false_eq = p.clone();
            if let Proposition::ConditionIs(_, truth) = &mut false_eq[0] {
                *truth = false;
            }
            assert!(check(0, &[0, 1], &false_eq, &result).is_err());
            let mut false_bound = p.clone();
            if let Proposition::ConditionIs(_, truth) = &mut false_bound[1] {
                *truth = false;
            }
            assert!(check(0, &[0, 1], &false_bound, &result).is_err());
            let mut false_result = result.clone();
            if let Proposition::ConditionIs(_, truth) = &mut false_result {
                *truth = false;
            }
            assert!(check(0, &[0, 1], &p, &false_result).is_err());
            let second_equality = if lower {
                equality(c.clone(), a.clone())
            } else {
                equality(a.clone(), c.clone())
            };
            let equality_result = if lower {
                equality(c.clone(), b.clone())
            } else {
                equality(b.clone(), c.clone())
            };
            let equalities = vec![eq.clone(), second_equality];
            assert_eq!(check(0, &[0, 1], &equalities, &equality_result), Ok(()));
            assert!(check(0, &[0, 1], &p, &equality_result).is_err());
            assert!(check(0, &[0, 1], &equalities, &result).is_err());
            let cert = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::IntegerRelationTransport {
                    bounds: vec![0, 1],
                    result: result.clone(),
                }],
                conclusion: 0,
            };
            assert!(cert.check(&result, &p).is_ok());
        }
    }
    let mut p = vec![equality(a.clone(), b.clone()), le(a.clone(), c.clone())];
    let result = le(b, c);
    for size in [4usize, 16, 64, 256] {
        while p.len() < size {
            p.push(le(
                IntegerTerm::constant(0.into()),
                IntegerTerm::constant(1.into()),
            ));
        }
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0, 1], &p, &result));
        checked.unwrap();
        assert_eq!(work, 5);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerRelationTransport {
                    bounds: vec![0, 1],
                    result: result.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&result, &p));
        checked.unwrap();
        assert_eq!(work, 5 * size + 1);
    }
}
