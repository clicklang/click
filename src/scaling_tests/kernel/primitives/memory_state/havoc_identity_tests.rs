// Scaling tests of `src/kernel/primitives/memory_state.rs` (module `havoc_identity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn havoc_write_set_identity_scales_near_linearly_with_term_size() {
    let samples = [32, 64, 128, 256]
        .into_iter()
        .map(|depth| {
            let range = range(depth, 1);
            let (identity, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory_havoc_write_set_identity(std::slice::from_ref(&range))
            });
            assert!(!identity.is_empty());
            assert!(work > 0);
            (depth, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
        "havoc identity work grew faster than near-linearly: {samples:?}"
    );
}
