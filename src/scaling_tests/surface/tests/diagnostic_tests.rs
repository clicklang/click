// Scaling tests of `src/surface/tests/diagnostic_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: growing generated loop-bundle expansion and checked work"]
fn wide_loop_invariant_bundle_expansion_work_scales_with_members() {
    let mut samples = Vec::new();
    for size in [32, 64, 128] {
        eprintln!("wide loop bundle size {size}: verify");
        let (source, proof) = wide_loop_invariant_fixture(size);
        let sources = [("bundle.c", source.as_str())];
        verify_c0_sources(&proof, &sources).unwrap();
        let (expanded, work) = crate::instrumentation::measure_deterministic_work(|| {
            eprintln!("wide loop bundle size {size}: expand");
            crate::surface::expand_c0_claim_source_by_label(&proof, &sources, "run.contract")
        });
        let expanded = expanded.unwrap();
        eprintln!("wide loop bundle size {size}: recheck ({work} units)");
        verify_c0_sources(&expanded, &sources).unwrap();
        assert!(work > 0);
        samples.push((size, work));
    }
    // Quadrupling input allows the logarithmic bundle-indexing factor and
    // fixed setup, but rejects quadratic expansion/checking growth.
    assert!(samples[2].1 <= samples[0].1 * 6, "{samples:?}");
}
