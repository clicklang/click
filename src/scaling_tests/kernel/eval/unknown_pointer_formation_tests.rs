use super::*;

#[test]
fn pointer_formation_uses_selected_bounds_beside_unrelated_ranges_and_facts() {
    let mut samples = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = pointer(931_000);
        let mut resources = ResourceContext::new().unchecked_with_fact(view(&p, 0, 3));
        let mut facts = PureFactContext::new();
        for i in 0..size {
            let other = pointer(932_000 + i);
            resources = resources.unchecked_with_fact(view(&other, 0, 3));
            facts = facts.assume_proposition(
                other
                    .opaque_coverage_fact(&CMemoryRange::from_pointer_value(
                        &other,
                        0u32.into(),
                        3u32.into(),
                        4,
                    ))
                    .unwrap(),
            );
        }
        resources.synchronize_memory_equalities(&facts);
        let (allowed, work) = crate::instrumentation::measure_deterministic_work(|| {
            permits(&p, 12, &facts, &resources)
        });
        assert!(allowed);
        assert!(!permits(&p, 16, &facts, &resources));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "formation searched unrelated bounds: {samples:?}"
    );
}
