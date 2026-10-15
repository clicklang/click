// Scaling tests of `src/surface/tests/back_edge_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn back_edge_work_scales_with_body_size() {
    let samples = [8, 128, 1024].map(|size| {
        let body = "i=i;".repeat(size) + "i=i+1;";
        let c = source(&body);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            verify_c0_sources(PROOF, &[("count.c", &c)])
        });
        result.unwrap();
        (size, work)
    });
    assert!(samples[0].1 > 0);
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) * 3,
            "{samples:?}"
        );
    }
}
