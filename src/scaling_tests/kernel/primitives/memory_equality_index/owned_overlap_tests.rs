use super::*;

#[test]
fn containing_owner_lookup_does_not_walk_nested_predecessors() {
    let mut samples = Vec::new();
    for count in [4_u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let base = at(7_001);
        let containing = owner(base.clone(), 0, 1_000_000);
        let frame = ResourceContext::new()
            .unchecked_with_fact(containing.clone())
            .unchecked_with_facts((0..count).map(|i| owner(base.clone(), 2 + 2 * i, 3 + 2 * i)));
        let query = owner(base, 8 + 2 * count, 9 + 2 * count);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast =
                crate::kernel::search::FastOperationScope::enter("cold containing owner lookup");
            frame.constant_owned_overlap(&query, &facts)
        });
        assert!(matches!(result, ConstantOwnedOverlap::Overlap(_)));
        let removed = frame
            .clone()
            .without_exact_representation(&containing)
            .unwrap();
        assert!(matches!(
            removed.constant_owned_overlap(&query, &facts),
            ConstantOwnedOverlap::Clear
        ));
        assert!(matches!(
            frame.constant_owned_overlap(&query, &facts),
            ConstantOwnedOverlap::Overlap(_)
        ));
        assert!(frame.memory_equalities.lock().unwrap().published.is_none());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "nested intervals: {samples:?}"
    );
}
