// Scaling tests of `src/kernel/proof/integer_division_bounds.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn division_bounds_work_is_independent_of_unused_facts_and_linear_in_nodes() {
    let (mut p, a, b) = inputs([-100, 100, 1, 10]);
    let result = goal(&a, &b, true, 9, false);
    let mut baseline = None;
    for size in [4usize, 16, 64, 256] {
        while p.len() < size {
            p.push(le(
                IntegerTerm::constant(0.into()),
                IntegerTerm::constant(1.into()),
            ));
        }
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1, 2, 3], &p, &result)
        });
        checked.unwrap();
        assert_eq!(*baseline.get_or_insert(work), work);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerDivisionBounds {
                    bounds: vec![0, 1, 2, 3],
                    result: result.clone()
                };
                size
            ],
            conclusion: size - 1,
        };
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| cert.check(&result, &p));
        checked.unwrap();
        assert_eq!(work, size * baseline.unwrap() + 1);
    }
}

#[test]
fn division_bounds_precharge_magnitude_work_and_enforce_its_budget() {
    let (_, a, b) = inputs([0, 0, 1, 1]);
    let mut previous = 0;
    for bits in [64usize, 128, 256, 512, 1024] {
        let maximum = BigInt::from(1) << bits;
        let p = vec![
            le(IntegerTerm::constant(-&maximum), a.clone()),
            le(a.clone(), IntegerTerm::constant(maximum.clone())),
            le(IntegerTerm::constant(BigInt::from(1)), b.clone()),
            le(b.clone(), IntegerTerm::constant(maximum.clone())),
        ];
        let result = le(
            IntegerTerm::truncating_quotient(a.clone(), b.clone()),
            IntegerTerm::constant(maximum),
        );
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1, 2, 3], &p, &result)
        });
        checked.unwrap();
        assert!(work > previous);
        if previous > 0 {
            assert!(work <= previous * 4);
        }
        previous = work;
        crate::instrumentation::with_run_work_limit(work - 1, || {
            assert_eq!(
                check(0, &[0, 1, 2, 3], &p, &result),
                Err(Error::WorkLimitExceeded)
            )
        });
        crate::instrumentation::with_run_work_limit(work, || {
            assert_eq!(check(0, &[0, 1, 2, 3], &p, &result), Ok(()))
        });
    }
}
