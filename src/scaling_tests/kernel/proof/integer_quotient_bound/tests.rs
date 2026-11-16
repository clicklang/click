// Scaling tests of `src/kernel/proof/integer_quotient_bound.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

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
