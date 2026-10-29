// Store footprint selection reads the written bases, not their alias classes.
#[test]
fn ownership_footprint_does_not_walk_pointer_aliases() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |i| Pointer::symbolic(Variable(991_000 + i));
            let owner = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new(pointer(0), 0u32.into(), 2u32.into()),
            ));
            let mut facts = PureFactContext::new()
                .assume_proposition(Proposition::CResourceComposition(owner.clone()))
                .with_store_owner(Some(owner));
            for i in 1..=size {
                let base = if related { pointer(0) } else { pointer(2 * i) };
                facts = facts
                    .assume_condition(ConditionTerm::pointer_equal(base, pointer(2 * i + 1)), true);
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        matches!(facts.owned_store_footprint(&pointer(0), 4), OwnedStoreFootprint::Members(m) if m.len() == 1)
                    );
                    assert!(
                        matches!(facts.owned_store_footprint(&pointer(3), 4), OwnedStoreFootprint::Members(m) if m.is_empty())
                    );
                }
            });
            samples.push((size, work));
        }
        assert!(
            samples.iter().all(|(_, work)| *work <= 200),
            "related={related}: {samples:?}"
        );
        eprintln!("written store ownership related={related}: {samples:?}");
    }
}
