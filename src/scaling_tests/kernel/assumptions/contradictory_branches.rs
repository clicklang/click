fn equality() -> ConditionTerm {
    ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(680_000)),
        Bitvector32Term::Variable(Variable(680_001)),
    )
}

#[test]
fn opposite_assumption_closes_only_its_branch_and_survives_reconstruction() {
    use crate::surface::planning::proposition_search::PropositionSearch;
    let goal = Proposition::Predicate {
        name: "unrelated_goal".into(),
        arguments: vec![],
    };
    for condition in [
        equality(),
        ConditionTerm::Variable(Variable(680_002)),
        ConditionTerm::Constant(false),
    ] {
        for first in [false, true] {
            let parent = PureFactContext::new().assume_condition(condition.clone(), first);
            let child = parent.clone().assume_condition(condition.clone(), !first);
            assert!(
                child.is_inconsistent(),
                "lost contradiction: {condition:?}, {first}"
            );
            assert!(child.proves_without_prop_facts(&goal));
            assert!(
                child
                    .condition_facts
                    .shares_root_with(&parent.condition_facts)
            );
            let proof = child.derive_proposition(&goal).expect("explosion proof");
            assert!(proof.check(&child));
            assert_eq!(parent.condition_facts.get(&condition), Some(&first));
            if !matches!(condition, ConditionTerm::Constant(_)) {
                assert!(!parent.is_inconsistent());
                assert!(!parent.proves_without_prop_facts(&goal));
                assert!(!proof.check(&parent));
                let without_false = child.without_exact_fact(&Proposition::ConditionIs(
                    ConditionTerm::Constant(false),
                    true,
                ));
                assert!(
                    !without_false.is_inconsistent(),
                    "remaining facts for {condition:?}, first={first}: {:?}; scalar conflict={}, constructors={:?}",
                    without_false.pure_facts(),
                    without_false.equality_graph.has_scalar_constant_conflict(),
                    without_false.algebraic_constructor_conflicts
                );
                assert!(!proof.check(&without_false));
            }
            let rebuilt = child
                .pure_facts()
                .into_iter()
                .fold(PureFactContext::new(), |context, fact| {
                    context.assume_proposition(fact)
                });
            assert!(rebuilt.is_inconsistent());
            assert!(rebuilt.proves_without_prop_facts(&goal));
            assert!(!child.restricted_to_facts(&[], &[]).is_inconsistent());
        }
    }
}

#[test]
fn contradictory_branch_creation_does_not_rebuild_ambient_indexes() {
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut parent = PureFactContext::new().assume_condition(equality(), true);
        for index in 0..size {
            parent = parent.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(681_000 + index)),
                    Bitvector32Term::Constant(1000),
                ),
                true,
            );
        }
        assert!(!parent.is_inconsistent());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                let child = parent.clone().assume_condition(equality(), false);
                std::hint::black_box(child.is_inconsistent());
            }
        });
        samples.push((size, work));
    }
    eprintln!("contradictory branch work: {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 16),
        "ambient rebuild: {samples:?}"
    );
}
