#[test]
fn constructed_normalization_bounds_neighbours_and_ignores_alias_classes() {
    for axis in ["duplicates", "adjacent", "aliases"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Pointer::symbolic(Variable(8_853_000));
            let mut facts = PureFactContext::new();
            if axis == "aliases" {
                for index in 0..count {
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(
                            pointer.clone(),
                            Pointer::symbolic(Variable(8_853_100 + u64::from(index))),
                        ),
                        true,
                    );
                }
            }
            let ranges = if axis == "aliases" { 2 } else { count };
            let context = ResourceContext::new_with_equalities(&facts).unchecked_with_facts(
                (0..ranges).map(|index| {
                    let start = if axis == "duplicates" { 0 } else { index };
                    ResourceFact::View(Resource::Memory(MemoryRange::new(
                        pointer.clone(),
                        start.into(),
                        (start + 1).into(),
                    )))
                }),
            );
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                let _fast = crate::kernel::search::FastOperationScope::enter(
                    "constructed body normalization",
                );
                context.normalized_without_discovery(&facts)
            });
            assert_eq!(normalized.facts().len(), 1);
            samples.push(work);
        }
        if axis == "aliases" {
            assert!(
                samples.iter().all(|work| *work <= samples[0] + 32),
                "{axis}: {samples:?}"
            );
        } else {
            assert!(samples[2] <= samples[0] * 24 + 64, "{axis}: {samples:?}");
        }
    }
}
