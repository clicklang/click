// Scaling tests of `src/kernel/resource_tracker/tests.rs` (module `saved_states`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// A question costs one keyed lookup per point, whatever the two states
/// hold. Growing the states by unrelated instances — what a question's
/// key is *not* — leaves the work
/// at two units, which is what would fail if this enumerated a resource
/// context instead of indexing it.
///
/// The deterministic work is measured, not estimated, and the question is
/// answered at every size so the curve cannot be flattened by a run that
/// decides nothing.
#[test]
fn a_saved_state_version_costs_one_lookup_per_point() {
    let unrelated = |size: u64, rank: u32| {
        let mut state = holding(1, rank, 0);
        for other in 0..size {
            state =
                state
                    .clone()
                    .with_resource_context(state.resources().clone().unchecked_with_fact(
                        CResourceFact::own(CResource::Instance(instance(100 + other, 7, 7))),
                    ));
        }
        state
    };
    for size in [8u64, 16, 32, 64] {
        let entry = unrelated(size, 3);
        let after = unrelated(size, 4);
        let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
            same_at_states(rank(), StatePoint::at(&after), StatePoint::at(&entry))
        });
        assert_eq!(
            outcome,
            replaced(None),
            "size {size} must still be answered, or the curve measures nothing"
        );
        assert_eq!(
            work, 2,
            "size {size} cost {work} units; a question is one keyed lookup per point"
        );
    }
}
