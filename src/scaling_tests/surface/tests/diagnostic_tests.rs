// Scaling tests of `src/surface/tests/diagnostic_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: growing generated loop-bundle expansion and checked work"]
fn wide_loop_invariant_bundle_expansion_work_scales_with_members() {
    let mut samples = Vec::new();
    for size in [32, 48, 64] {
        let (source, proof) = wide_loop_invariant_fixture(size);
        let sources = [("bundle.c", source.as_str())];
        // Expansion constructs a checked proof of the original claim. Retain
        // the independent cold check of its output below without first running
        // the same original claim a second time.
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
    // Proof shape changes can make adjacent work non-monotonic, so
    // compare the retained endpoints rather than subtracting increments.
    // For B + k*N + a*N^2, the old sixfold 32-to-128 guard allowed
    // a <= B/2048 + k/160. The 19/10 guard at 32/64 allows only
    // a <= 3*B/7168 - k/672, a stricter bound for B,k >= 0.
    let bounded = |work: &[(usize, usize)]| work[2].1 * 10 <= work[0].1 * 19;
    assert!(
        bounded(&samples),
        "wide-bundle work grew too quickly: {samples:?}"
    );
    // The old observed curve was 152088/211960/507978 at 32/64/128.
    // Forty additional units per squared member made its original guard
    // fail. Keep sensitivity to that same added quadratic scan here.
    let quadratic = samples
        .iter()
        .map(|&(size, work)| (size, work + 40 * size * size))
        .collect::<Vec<_>>();
    assert!(
        !bounded(&quadratic),
        "the smaller grid must detect the original quadratic crossover: {samples:?}"
    );
}
