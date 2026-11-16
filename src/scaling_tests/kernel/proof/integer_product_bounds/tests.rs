// Scaling tests of `src/kernel/proof/integer_product_bounds.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn product_bounds_precharge_big_integer_work_and_stop_before_arithmetic() {
    let (x, y) = variables();
    let mut previous = 0;
    for bits in [64usize, 128, 256, 512, 1024] {
        let limit = BigInt::from(1) << bits;
        let premises = inputs(&x, &y, &[-&limit, limit.clone(), -&limit, limit.clone()]);
        let result = goal(&x, &y, &limit * &limit, false);
        let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(0, &[0, 1, 2, 3], &premises, &result)
        });
        assert_eq!(checked, Ok(()));
        assert!(work > previous);
        if previous != 0 {
            assert!(work <= previous * 4);
        }
        previous = work;
        crate::instrumentation::with_run_work_limit(work - 1, || {
            assert_eq!(
                check(0, &[0, 1, 2, 3], &premises, &result),
                Err(Error::WorkLimitExceeded)
            );
        });
        crate::instrumentation::with_run_work_limit(work, || {
            assert_eq!(check(0, &[0, 1, 2, 3], &premises, &result), Ok(()));
        });
    }
}
