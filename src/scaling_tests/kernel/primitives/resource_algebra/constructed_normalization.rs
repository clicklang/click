#[test]
fn constructed_normalization_bounds_neighbours_and_ignores_alias_classes() {
    for axis in ["duplicates", "adjacent", "aliases"] {
        let mut samples = Vec::new();
        for count in [4_u32, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = Address::symbolic(Variable(8_853_000));
            let mut facts = PureFactContext::new();
            if axis == "aliases" {
                for index in 0..count {
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(
                            pointer.clone(),
                            Address::symbolic(Variable(8_853_100 + u64::from(index))),
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

#[test]
fn singleton_normalization_retains_occurrences_without_alias_discovery() {
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = Address::symbolic(Variable(8_963_000));
        let facts = (0..count).fold(PureFactContext::new(), |facts, i| {
            facts.assume_condition(
                ConditionTerm::pointer_equal(p.clone(), Address::symbolic(Variable(8_963_100 + i))),
                true,
            )
        });
        let owner = ResourceFact::own_memory(MemoryRange::new(p, 0u32.into(), 1u32.into()));
        let context =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner.clone());
        let occurrence = context.unique_owned_occurrence_for_fact(&owner).unwrap().0;
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast = crate::kernel::search::FastOperationScope::enter(
                "singleton ownership normalization",
            );
            context.normalized(&facts)
        });
        assert_eq!(
            normalized.owned_fact_for_occurrence(occurrence),
            Some(&owner)
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "singleton aliases: {samples:?}"
    );
}

#[test]
fn constructed_normalization_omits_only_proven_empty_ranges() {
    let start = MachineTerm::Variable(Variable(8_968_000));
    let end = MachineTerm::Variable(Variable(8_968_001));
    let range = ResourceFact::own_memory(MemoryRange::new(
        Address::symbolic(Variable(8_968_002)),
        start.clone(),
        end.clone(),
    ));
    let equal = |left, right| {
        ConditionTerm::machine_compare(
            MachineIntegerType::Int32,
            CompareRelation::Equal,
            left,
            right,
        )
    };
    let work = [4_u64, 16, 64].map(|count| {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = (0..count).fold(PureFactContext::new(), |facts, index| {
            let adjacent = MachineTerm::Variable(Variable(8_968_100 + index));
            let unrelated = MachineTerm::Variable(Variable(8_968_200 + index));
            facts
                .assume_condition(equal(end.clone(), adjacent), true)
                .assume_condition(
                    ConditionTerm::signed_less_equal(0u32.into(), unrelated),
                    true,
                )
        });
        let retained = coalesce_written_resource_descriptions(vec![range.clone()], &facts);
        assert_eq!(retained, [range.clone()]);
        let facts = facts.assume_condition(equal(start.clone(), end.clone()), true);
        let (empty, work) = crate::instrumentation::measure_deterministic_work(|| {
            coalesce_written_resource_descriptions(vec![range.clone()], &facts)
        });
        assert!(empty.is_empty());
        work
    });
    assert_eq!(work, [work[0]; 3], "empty-range normalization: {work:?}");
}
