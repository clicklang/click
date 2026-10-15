// Scaling tests of `src/surface/checking/integer_affine_planner.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Elimination is quadratic in the explicitly listed premises, not
/// exponential: each listed equality is reduced by the rows already built,
/// and each row operation is one bounded pass over the claim's atoms. A
/// unit pivot never grows a coefficient, so doubling the listed slice may
/// at most quadruple the work.
#[test]
fn eliminating_a_longer_chain_stays_quadratic_in_the_listed_premises() {
    let mut samples = Vec::new();
    for (index, length) in [4usize, 8, 16, 32].into_iter().enumerate() {
        let (goal, premises) = equality_chain(5_000 + 1_000 * index as u64, length);
        let (plan, work) = crate::instrumentation::measure_deterministic_work(|| {
            plan_integer_affine_certificate(&goal, &premises)
        });
        let plan = plan.expect("a chain of any listed length should be eliminated");
        plan.check(&goal, &premises)
            .expect("every chain length should verify");
        samples.push((length, work));
    }
    for window in samples.windows(2) {
        let (smaller, smaller_work) = window[0];
        let (larger, larger_work) = window[1];
        assert!(
            larger_work <= 4 * smaller_work + 1_024,
            "doubling the listed slice from {smaller} to {larger} multiplied planner work \
             by more than four: {samples:?}"
        );
    }
}
