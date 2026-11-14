#[test]
fn pointer_decision_miss_does_not_walk_owned_anchor_aliases() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let (left, right) = (pointer(1), pointer(2));
        let mut facts =
            PureFactContext::new().assume_proposition(owner_of(&[left.clone(), pointer(3)]));
        for index in 0..size {
            facts = facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), pointer(100 + index)),
                true,
            ));
        }
        let condition = ConditionTerm::pointer_equal(left, right);
        let (decision, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&condition));
        assert_eq!(decision, None);
        samples.push((size, work));
    }
    eprintln!("pointer decision miss work: {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 4),
        "fixed pointer decision walked ambient aliases: {samples:?}"
    );
}

#[test]
fn explicit_separation_decides_pointers_without_composition_discovery() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let (left, right) = (pointer(1), pointer(2));
        let mut facts =
            PureFactContext::new().assume_proposition(owner_of(&[left.clone(), right.clone()]));
        for index in 0..size {
            facts = facts.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.clone(), pointer(100 + index)),
                true,
            ));
        }
        let condition = ConditionTerm::pointer_equal(left.clone(), right.clone());
        let _fast = crate::kernel::search::FastOperationScope::enter("explicit pointer separation");
        assert_eq!(facts.decide(&condition), None);
        let cell = |pointer| {
            Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                pointer,
                0u32.into(),
                1u32.into(),
                8,
            )))
        };
        let facts = facts.assume_proposition(Proposition::CResourceSeparate {
            left: cell(left.clone()),
            right: cell(right),
        });
        let (decision, work) =
            crate::instrumentation::measure_deterministic_work(|| facts.decide(&condition));
        assert_eq!(decision, Some(false));
        assert_eq!(
            facts.decide(&ConditionTerm::pointer_equal(left.clone(), left)),
            Some(true)
        );
        samples.push((size, work));
    }
    eprintln!("explicit pointer separation work: {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 4),
        "explicit separation walked ambient aliases: {samples:?}"
    );
}
