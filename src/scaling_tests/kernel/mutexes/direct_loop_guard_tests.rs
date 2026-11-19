// Scaling tests of `src/kernel/mutexes/direct_loop_guard_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn direct_loop_guard_lookup_ignores_unrelated_mutexes() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut context = MutexContext::new(entry());
        for index in 1..size {
            context = context.initialize_empty(address(index), 40).unwrap();
        }
        let top = head(context.state(), 706);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            MutexContext::new(top).acquire_current(&address(0), &PureFactContext::new())
        });
        assert!(result.is_ok());
        measurements.push(work);
    }
    assert!(
        measurements[3] <= measurements[0] * 2 + 64,
        "indexed lookup work grew with unrelated mutexes: {measurements:?}"
    );
}

#[test]
fn conditional_guard_open_and_backedge_ignore_unrelated_resources() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let mut initial = entry();
        for index in 0..size {
            initial.resources =
                initial
                    .resources
                    .unchecked_with_fact(ResourceFact::own(Resource::Token {
                        name: format!("unrelated_{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let top = head(&initial, 720);
        let (next, open_work) = crate::instrumentation::measure_deterministic_work(|| {
            MutexContext::new(top.clone())
                .acquire_current(&address(0), &PureFactContext::new())
                .unwrap()
        });
        let next = next.state().clone().with_local("flag", int32(1));
        let (result, close_work) = crate::instrumentation::measure_deterministic_work(|| {
            normalize_direct_loop_guards(&top, &next, &PureFactContext::new())
        });
        assert!(result.is_ok());
        measurements.push(open_work + close_work);
    }
    assert!(
        measurements[2] <= measurements[0] * 2 + 64,
        "unrelated resource work: {measurements:?}"
    );
}

#[test]
fn conditional_guard_duplicate_refusal_does_not_walk_related_occurrences() {
    let top = head(&entry(), 721);
    let owned = ResourceFact::own(Resource::ConditionalMutexGuard(carrier(&top)));
    let mut measurements = Vec::new();
    for size in [16, 64, 256] {
        let mut resources = ResourceContext::new();
        for _ in 0..size {
            resources = resources.unchecked_with_fact(owned.clone());
        }
        let ((selected, invalid), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (
                    resources.unique_owned_occurrence_for_fact(&owned),
                    resources.validity_error(&PureFactContext::new()),
                )
            });
        assert!(selected.is_none());
        assert!(invalid.is_some());
        measurements.push(work);
    }
    assert!(
        measurements[2] <= measurements[0] * 2 + 16,
        "related occurrence work: {measurements:?}"
    );
}
