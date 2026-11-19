// Scaling regressions for ordinary Integer composition: source DAG sharing
// and fixed explicit operations beside growing related/unrelated contexts.

#[test]
fn integer_composition_shared_nodes_have_polynomial_output_and_checking_work() {
    let samples = [2, 4, 8].map(|depth| shared_plan(depth, 0, false));
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= 6 * pair[0].0,
            "shared checking expanded a tree: {samples:?}"
        );
        assert!(
            pair[1].1 <= 6 * pair[0].1,
            "shared proof text expanded a tree: {samples:?}"
        );
        assert!(
            pair[1].2 <= 3 * pair[0].2,
            "each node must be emitted once: {samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: six context controls take 1.2s in parallel"]
fn integer_composition_checking_ignores_growing_related_and_unrelated_contexts() {
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| shared_plan(1, size, related).0);
        assert!(
            samples.iter().all(|work| *work <= 2 * samples[0]),
            "composition scanned facts (related={related}): {samples:?}"
        );
    }
}
