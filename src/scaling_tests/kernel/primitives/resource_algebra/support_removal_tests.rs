// Scaling tests of `src/kernel/primitives/resource_algebra.rs` (module `support_removal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn frame_exchange_preserves_occurrences_and_does_not_scan_unrelated_frame() {
    let assumptions = PureFactContext::new();
    let before = CResourceFact::own_composite("before".into(), Vec::new());
    let after = CResourceFact::own_composite("after".into(), Vec::new());
    let body = ResourceContext::new().unchecked_with_fact(before.clone());
    let exit = body
        .clone()
        .without_exact_representation(&before)
        .unwrap()
        .unchecked_with_fact(after.clone());
    let occurrence = exit.unique_owned_occurrence_for_fact(&after).unwrap();
    let mut measurements = Vec::new();
    for size in [8, 32, 128] {
        let mut frame = body.clone();
        for index in 0..size {
            frame = frame.unchecked_with_fact(CResourceFact::own_composite(
                format!("frame_{index}"),
                Vec::new(),
            ));
        }
        let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
            exit.restore_frame_after_exchange(&body, &frame, &assumptions)
                .unwrap()
        });
        assert!(!restored.contains_exact_representation(&before));
        assert_eq!(
            restored.unique_owned_occurrence_for_fact(&after),
            Some(occurrence)
        );
        assert_eq!(restored.facts().len(), size + 1);
        measurements.push(work);
    }
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}
