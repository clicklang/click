// Scaling tests of `src/kernel/equality_graph/inputs.rs` (module `read_trace_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn admitted_read_trace_walks_only_the_selected_delta() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let mut graph = EqualityGraph::default();
        for index in 0..size {
            graph.add_equality(&pointer(301_000 + index * 2), &pointer(301_001 + index * 2));
        }
        let checkpoint = graph.read_equality_checkpoint();
        graph.add_checked_read_equality(&pointer(302_000), &pointer(302_001));
        graph.add_equality(&pointer(302_002), &pointer(302_003));
        let (delta, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.read_equalities_since(&checkpoint)
        });
        assert_eq!(
            delta.equalities,
            vec![equality(pointer(302_000), pointer(302_001))]
        );
        samples.push(work);
    }
    assert_eq!(samples, vec![2, 2, 2]);
}
