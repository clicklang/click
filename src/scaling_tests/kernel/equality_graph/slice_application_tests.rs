// Scaling tests of `src/kernel/equality_graph/slice_application_tests.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// Reading `f(x).len()` and asking the count equality an unfolding of
/// `f(x)` gives do not grow with unrelated slice applications and their
/// unfoldings (`design/rust-slice-values.md`, step 2b-iii-b-ii).
#[test]
fn slice_application_counts_ignore_unrelated_applications() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            let unrelated = slice_of(&format!("unrelated_{index}"), 957_000 + index);
            let body = wide(958_000 + 2 * index, 958_001 + 2 * index);
            context = context.assume_condition(complete_equal(&unrelated, &body), true);
        }
        let (application, body) = (slice_of("bytes_of", 959_000), wide(959_001, 959_002));
        let context = context.assume_condition(complete_equal(&application, &body), true);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let length = application.len().expect("a slice has a count");
            assert_eq!(length, &count_of("bytes_of", 959_000));
            assert!(
                context
                    .equality_graph
                    .are_uint64_equal(length, &count(959_002))
            );
        });
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] + 8, "{costs:?}");
    }
}

/// Interning the counts of `size` distinct applications costs a constant
/// amount each: the work grows linearly, with no scan of earlier ones.
#[test]
fn interning_application_counts_grows_linearly() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(|size| {
        let counts = (0..size)
            .map(|index| count_of("bytes_of", 960_000 + index))
            .collect::<Vec<_>>();
        let mut graph = EqualityGraph::default();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for pair in counts.windows(2) {
                graph.add_uint64_equality(&pair[0], &pair[1]);
            }
        });
        assert!(graph.are_uint64_equal(&counts[0], &counts[counts.len() - 1]));
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{costs:?}");
    }
}
