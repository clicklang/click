// Scaling tests of `src/kernel/proof/integer_quotient_bound.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn quotient_bound_work_is_local_and_linear_in_certificate_nodes() {
    let (mut p, result) = case(v(198003), v(198002), true);
    let (checked, single) =
        crate::instrumentation::measure_deterministic_work(|| check(0, &[0, 1], &p, &result));
    checked.unwrap();
    for size in [4, 16, 64, 256] {
        p.resize(size, le(c(0), c(1)));
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0, 1], &p, &result));
        checked.unwrap();
        assert_eq!(work, single);
        let cert = SpecialArithmeticCertificate {
            nodes: vec![
                SpecialArithmeticNode::IntegerQuotientBound {
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
        assert_eq!(work, single * size + 1);
    }
    for depth in [4, 16, 64, 256] {
        let mut bound = v(198003);
        for _ in 0..depth {
            bound = IntegerTerm::add(bound.clone(), bound);
        }
        let (p, result) = case(bound, v(198002), true);
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0, 1], &p, &result));
        checked.unwrap();
        assert_eq!(work, single);
    }
}

#[test]
fn quotient_bound_constant_magnitudes_are_precharged() {
    for bits in [64usize, 256, 1024, 4096] {
        let b: BigInt = BigInt::from(1) << bits;
        let (p, result) = case(IntegerTerm::constant(b), c(3), false);
        let (checked, work) =
            crate::instrumentation::measure_deterministic_work(|| check(0, &[0, 1], &p, &result));
        checked.unwrap();
        assert!(work >= bits);
        assert_eq!(
            crate::instrumentation::with_run_work_limit(work, || check(0, &[0, 1], &p, &result)),
            Ok(())
        );
        assert_eq!(
            crate::instrumentation::with_run_work_limit(work - 1, || check(
                0,
                &[0, 1],
                &p,
                &result
            )),
            Err(Error::WorkLimitExceeded)
        );
    }
}
