// Scaling tests of `src/surface/checking/integer_refutation_planner.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn work_grows_linearly_with_independent_unused_premises() {
    let mut samples = Vec::new();
    for size in [8u64, 16, 32, 64] {
        let mut premises = vec![le(x(50), x(51)), le(x(51), c(3))];
        for extra in 0..size {
            premises.push(le(x(1000 + extra), c(extra as i64)));
        }
        let goal = le(x(50), c(3));
        let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_integer_refutation(&goal, &premises)
        });
        assert!(matches!(outcome, IntegerRefutation::Proved { .. }));
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 3 * pair[0], "{samples:?}");
    }
}
