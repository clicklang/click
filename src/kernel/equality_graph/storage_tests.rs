use super::*;

#[test]
fn concrete_storage_coordinates_follow_transitive_aliases_and_forks() {
    let first = Pointer::symbolic(Variable(896_000));
    let second = Pointer::symbolic(Variable(896_001));
    let storage = Pointer {
        block: "local:mutex".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let empty = PureFactContext::new();
    let joined = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(first.clone(), second.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(second, storage.clone()), true);
    assert_eq!(
        joined
            .equality_graph
            .storage_address(&first.offset_by_bytes(16)),
        storage.offset_by_bytes(16)
    );
    assert_eq!(empty.equality_graph.storage_address(&first), first);
    let other = Pointer {
        block: "local:other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let ambiguous = joined
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(first.clone(), other), true);
    assert_eq!(ambiguous.equality_graph.storage_address(&first), first);
    assert_eq!(joined.equality_graph.storage_address(&first), storage);
}

#[test]
fn external_addresses_select_their_own_concrete_storage_anchor() {
    let first = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(896_010)),
    };
    let second = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(896_011)),
    };
    let one = Pointer {
        block: "global:first".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let two = Pointer {
        block: "global:second".into(),
        offset: PointerOffsetTerm::Constant(16),
    };
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(first.clone(), one.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(second.clone(), two.clone()),
            true,
        );
    assert!(facts.equality_graph.are_equal(&first, &one));
    assert!(facts.equality_graph.are_equal(&second, &two));
    assert_eq!(
        facts
            .equality_graph
            .storage_address(&first.offset_by_bytes(4)),
        one.offset_by_bytes(4)
    );
    assert_eq!(
        facts
            .equality_graph
            .storage_address(&second.offset_by_bytes(8)),
        two.offset_by_bytes(8)
    );
}

#[test]
fn concrete_storage_lookup_does_not_walk_alias_history() {
    let root = Pointer::symbolic(Variable(896_100));
    let storage = Pointer {
        block: "local:indexed".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(root.clone(), storage.clone()),
            true,
        );
        for id in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    root.clone(),
                    Pointer::symbolic(Variable(897_000 + id)),
                ),
                true,
            );
        }
        let query = Pointer::symbolic(Variable(897_000 + size)).offset_by_bytes(8);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.equality_graph.storage_address(&query),
                storage.offset_by_bytes(8)
            );
        });
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 40,
        "storage query walked the equality history: {samples:?}"
    );
}

#[test]
fn alignment_uses_the_checked_storage_anchor_through_transitive_equality() {
    let first = Pointer::symbolic(Variable(896_900));
    let last = Pointer::symbolic(Variable(896_901));
    let storage = Pointer {
        block: PointerBlock::Heap(896_990),
        offset: PointerOffsetTerm::Constant(0),
    };
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(first.clone(), storage), true)
        .assume_condition(ConditionTerm::pointer_equal(last.clone(), first), true);
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(last.offset_by_bytes(8), 8)),
        Some(true)
    );
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(last.offset_by_bytes(8), 16)),
        Some(false)
    );
    assert_eq!(empty.decide(&ConditionTerm::pointer_aligned(last, 8)), None);
}

#[test]
fn declared_alignment_follows_late_transitive_address_equality() {
    let base = Pointer::symbolic(Variable(898_100));
    let middle = Pointer::symbolic(Variable(898_101));
    let alias = Pointer::symbolic(Variable(898_102));
    let original = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_aligned(base.clone(), 8), true);
    let facts = original
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(base, middle.clone()), true)
        .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
    assert_eq!(
        facts.decide(&ConditionTerm::pointer_aligned(alias.clone(), 8)),
        Some(true)
    );
    // The single-premise formation certificate must not silently omit the
    // equalities required by this stronger ambient graph decision.
    assert!(
        facts
            .pointer_alignment_certificate_decision(&alias, 8)
            .is_none()
    );
    assert_eq!(
        original.decide(&ConditionTerm::pointer_aligned(alias, 8)),
        None
    );
}

#[test]
fn declared_alignment_lookup_does_not_walk_alias_history() {
    let root = Pointer::symbolic(Variable(899_100));
    let mut work = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for id in 1..=size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    root.clone(),
                    Pointer::symbolic(Variable(900_000 + id)),
                ),
                true,
            );
        }
        // Register after all equality merges as well as before them above.
        facts = facts.assume_condition(ConditionTerm::pointer_aligned(root.clone(), 16), true);
        let query = Pointer::symbolic(Variable(900_000 + size)).offset_by_bytes(8);
        let (_, units) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts.decide(&ConditionTerm::pointer_aligned(query.clone(), 8)),
                Some(true)
            );
            assert_eq!(
                facts.decide(&ConditionTerm::pointer_aligned(query, 16)),
                Some(false)
            );
        });
        work.push(units);
    }
    assert!(
        work[3] <= work[0] + 80,
        "alignment walked aliases: {work:?}"
    );
}
