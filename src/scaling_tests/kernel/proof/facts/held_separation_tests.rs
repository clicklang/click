// Scaling tests of `src/kernel/proof/facts.rs` (module `held_separation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Same-block unrelated members must not turn one selected observation
/// into a frame scan or an enumeration of ownership pairs.
#[test]
fn held_separation_uses_only_the_selected_members() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| CResourceFact::own(cell(index))));
        let state = CState::new().with_resource_context(resources);
        let facts = ProofFacts::default();
        let goal = separation(cell(size - 2), cell(size - 1));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let observed = facts.with_selected_held_resource_separation(&goal, &state);
            assert!(observed.contains(&goal));
            assert_eq!(observed.fact_count(), 1);
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "selected separation inspected unrelated ownership: {samples:?}"
    );
}

#[test]
fn held_field_separation_does_not_visit_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let state =
            CState::new().with_resource_context(ResourceContext::new().unchecked_with_facts(
                (0..size).map(|index| CResourceFact::own(range(index, 0, 6, 4))),
            ));
        let goal = separation(range(size - 2, 1, 2, 8), range(size - 1, 0, 1, 8));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                ProofFacts::default()
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "selected fields visited unrelated owners: {samples:?}"
    );
}
