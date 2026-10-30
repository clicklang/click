// A claim checks its written domains, not every fact accumulated by the proof.
#[test]
fn claim_requirements_use_indexed_facts_and_scale_with_their_output() {
    let mut ambient_samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Bitvector32Term::Variable(Variable(992_000));
        let required = Proposition::ConditionIs(
            ConditionTerm::equal(variable.clone(), Bitvector32Term::Constant(7)),
            true,
        );
        let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&required));
        for index in 0..size {
            for left in [
                variable.clone(),
                Bitvector32Term::Variable(Variable(993_000 + index)),
            ] {
                facts = facts.with_kernel_checked_fact(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        left,
                        Bitvector32Term::Constant(1000 + index as u32),
                    ),
                    true,
                ));
            }
        }
        let goal = CClaimGoal {
            target: CFunctionContractClaimTarget::EnsureProposition(0),
            proposition: required.clone(),
            facts: vec![],
            obligations: vec![ProofObligation::verification_condition(required)],
        };
        // The deferred identity index pays for its explicit input once.
        // Cloned proof roots share it; subsequent checks must not revisit
        // ambient history.
        let (_, preparation) = crate::instrumentation::measure_deterministic_work(|| {
            facts.assumptions().build_stated_proposition_index();
        });
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                let clone = facts.clone();
                assert!(goal.unproved_requirements(clone.assumptions()).is_empty());
            }
        });
        ambient_samples.push((size, preparation, work));
    }
    assert!(
        ambient_samples[2].2 <= ambient_samples[0].2 * 2 + 16,
        "{ambient_samples:?}"
    );

    for pair in ambient_samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 5 + 16,
            "context preparation: {ambient_samples:?}"
        );
    }

    let mut output_samples = Vec::new();
    for size in [16u64, 32, 64, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let goal = CClaimGoal {
            target: CFunctionContractClaimTarget::EnsureProposition(0),
            proposition: Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            facts: vec![],
            obligations: (0..size)
                .map(|index| {
                    ProofObligation::verification_condition(Proposition::ConditionIs(
                        ConditionTerm::equal(
                            Bitvector32Term::Variable(Variable(994_000 + index)),
                            Bitvector32Term::Constant(7),
                        ),
                        true,
                    ))
                })
                .collect(),
        };
        let facts = PureFactContext::new();
        let (pending, work) = crate::instrumentation::measure_deterministic_work(|| {
            goal.unproved_requirements(&facts)
        });
        assert_eq!(pending.len(), size as usize);
        output_samples.push((size, work));
    }
    for pair in output_samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 3 + 16, "{output_samples:?}");
    }
}
