// Scaling tests of `src/kernel/assumptions.rs` (module `exact_materialization_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn exact_materialization_work_scales_near_linearly_with_chain_length() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|length| {
            let chain = load_chain(length, 23);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                exact_materialized_load_fixed_point(&chain)
            });
            assert_eq!(result, Bitvector32Term::Constant(23));
            assert!(work > 0);
            (length, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
        "exact materialization grew faster than near-linearly: {samples:?}"
    );
}
