// Scaling tests of `src/kernel/equality_graph/wide_pointer_tests.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// A chain of equalities among `size` wide pointers: each one merges one
/// more count pair, so total work grows linearly (`design/rust-slice-values.md`,
/// "Design check").
#[test]
fn wide_pointer_equality_chains_grow_linearly() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(|size| {
        let pointers = (0..size)
            .map(|index| wide(951_000 + index, 952_000 + index))
            .collect::<Vec<_>>();
        let mut graph = EqualityGraph::default();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for pair in pointers.windows(2) {
                graph.add_pointer_equality(&pair[0], &pair[1]);
            }
        });
        assert!(graph.are_uint64_equal(&count(952_000), &count(952_000 + size - 1)));
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{costs:?}");
    }
}

/// Reading `s.len()` and `s.as_ptr()` and asking the count equality a stated
/// `s == t` gives do not grow with unrelated wide-pointer facts.
#[test]
fn wide_pointer_components_ignore_unrelated_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            let (a, b) = (
                wide(953_000 + 2 * index, 954_000 + 2 * index),
                wide(953_001 + 2 * index, 954_001 + 2 * index),
            );
            context = context.assume_condition(complete_equal(&a, &b), true);
        }
        let (s, t) = (wide(955_000, 955_010), wide(955_001, 955_011));
        let context = context.assume_condition(complete_equal(&s, &t), true);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(s.len(), Some(&count(955_010)));
            assert!(s.as_ptr().len().is_none());
            assert!(
                context
                    .equality_graph
                    .are_uint64_equal(s.len().unwrap(), t.len().unwrap())
            );
        });
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] + 8, "{costs:?}");
    }
}

/// Whether two slices match in everything but their address reads their
/// counts' classes: one indexed lookup. It stays flat as unrelated slice
/// facts grow and as the chain of count equalities that makes the two
/// counts one class grows (`design/rust-slice-values.md`, "Design check").
#[test]
fn wide_pointer_value_matches_stay_flat() {
    let _session = crate::kernel::VerificationSession::enter();
    let costs = [8u64, 32, 128].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            let (a, b) = (
                wide(956_000 + 2 * index, 957_000 + 2 * index),
                wide(956_001 + 2 * index, 957_001 + 2 * index),
            );
            context = context.assume_condition(complete_equal(&a, &b), true);
        }
        // Related input: the counts are equal through a chain of `size`.
        for index in 0..size {
            context = context.assume_condition(
                OldConditionTerm::uint64_equal(count(958_000 + index), count(958_001 + index)),
                true,
            );
        }
        let (s, t) = (wide(959_000, 958_000), wide(959_000, 958_000 + size));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.pointer_provenance_match(&s, &t));
            assert!(!context.pointer_provenance_match(&s, &s.as_ptr()));
        });
        work
    });
    for pair in costs.windows(2) {
        assert!(pair[1] <= pair[0] + 8, "{costs:?}");
    }
}
