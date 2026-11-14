use super::*;

#[test]
fn claim_closing_updates_only_selected_entries_and_preserves_forks() {
    for count in [16_usize, 64, 256, 512] {
        let outcome = outcome();
        let original = OutcomeClaimGoals::open(
            (0..count).map(|index| (FunctionContractClaimKey::Ensure(index), None)),
            false,
        );
        let ((closed, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut current = original.clone();
                // Out-of-order closing must retain the first open source position.
                for index in (0..count).rev() {
                    let key = FunctionContractClaimKey::Ensure(index);
                    assert_eq!(current.first_open_position(), Some(0));
                    current = current.close(&key, receipt(), &outcome.identity).unwrap();
                    assert!(current.evidence(&key).is_some());
                }
                current
            })
        });
        assert!(work >= count, "entry updates must be charged");
        assert!(work <= 8 * count, "{count} claims charged {work} work");
        assert!(
            indexed_work <= 20 * count * (count.ilog2() as usize + 1),
            "{count} claims visited {indexed_work} index nodes"
        );
        assert_eq!(closed.first_open_position(), None);
        assert_eq!(original.first_open_position(), Some(0));
        assert!(
            original
                .evidence(&FunctionContractClaimKey::Ensure(count - 1))
                .is_none()
        );
        let sibling = original
            .close(
                &FunctionContractClaimKey::Ensure(0),
                receipt(),
                &outcome.identity,
            )
            .unwrap();
        assert_eq!(sibling.first_open_position(), Some(1));
        assert!(
            sibling
                .evidence(&FunctionContractClaimKey::Ensure(count - 1))
                .is_none()
        );
        let (((), work), indexed_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    closed
                        .evidence(&FunctionContractClaimKey::Ensure(count - 1))
                        .is_some()
                );
                assert!(
                    closed
                        .evidence(&FunctionContractClaimKey::Ensure(count))
                        .is_none()
                );
                assert!(
                    closed
                        .target(&FunctionContractClaimKey::Ensure(count))
                        .is_none()
                );
            })
        });
        assert_eq!(work, 3);
        assert!(indexed_work <= 6 * (count.ilog2() as usize + 1));
    }
}

#[test]
fn outcome_goal_selection_ignores_closed_claims_and_unrelated_proof_facts() {
    let execution = closing_execution();
    let context = crate::kernel::ContractClosingContext::new(&execution);
    let core = outcome();
    for count in [16, 64, 256, 512] {
        let mut claims = OutcomeClaimGoals::open(
            (0..count).map(|index| (FunctionContractClaimKey::Ensure(index), None)),
            false,
        );
        let mut goal =
            FunctionOutcomeObligation::new(0, Arc::new(OutcomeProofState::new(core.clone(), ())));
        goal.closing = Some(context.open(0, &core));
        goal.claims = Some(claims.clone());
        assert_eq!(
            goal.first_open_goal(),
            Ok(Some(OutcomeGoal::Claim {
                position: 0,
                key: FunctionContractClaimKey::Ensure(0)
            }))
        );
        for index in 0..count {
            claims = claims
                .close(
                    &FunctionContractClaimKey::Ensure(index),
                    receipt(),
                    &core.identity,
                )
                .unwrap();
        }
        goal.claims = Some(claims);
        for fact_count in [0, 64, 1024] {
            let facts = (0..fact_count).fold(
                crate::kernel::proof::ProofFacts::from_ordered(&[]),
                |facts, index| {
                    facts.with_fact(crate::kernel::Proposition::ConditionIs(
                        crate::kernel::ConditionTerm::equal(
                            crate::kernel::MachineTerm::Variable(crate::kernel::Variable(
                                976_000 + index,
                            )),
                            crate::kernel::MachineTerm::constant(0),
                        ),
                        true,
                    ))
                },
            );
            let proof = crate::kernel::proof::ProofObject::root(
                (),
                crate::kernel::proof::ProofBranch::new(
                    ProofObligation::<(), _>::FunctionOutcome(goal.clone()),
                    crate::kernel::proof::ProofBranchState::<()> {
                        facts,
                        unfolded_predicates: crate::kernel::proof::PersistentOrderedSet::default(),
                        execution: None,
                    },
                ),
            );
            let ((result, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    proof.complete_function_outcome()
                })
            });
            assert!(
                indexed_work <= 10 * (count.ilog2() as usize + 1),
                "{indexed_work} index visits for {count} claims"
            );
            assert!(result.is_err());
            assert_eq!(
                work, 2,
                "{count} closed claims, {fact_count} unrelated facts"
            );
        }
    }
}

#[test]
fn ordinary_closing_steps_ignore_unrelated_facts_and_closed_source_claims() {
    let execution = closing_execution();
    let path = &execution.paths()[0];
    let specification =
        crate::kernel::CheckedPathSpecification::new(execution.function(), path).unwrap();
    let core = outcome();
    let fact_sets = [0, 64, 1024].map(|fact_count| {
        (
            fact_count,
            (0..fact_count).fold(
                crate::kernel::proof::ProofFacts::from_ordered(&[]),
                |facts, index| {
                    facts.with_fact(crate::kernel::Proposition::ConditionIs(
                        crate::kernel::ConditionTerm::equal(
                            crate::kernel::MachineTerm::Variable(crate::kernel::Variable(
                                978_000 + index,
                            )),
                            crate::kernel::MachineTerm::constant(0),
                        ),
                        true,
                    ))
                },
            ),
        )
    });
    let mut baseline = None;
    for count in [16, 64, 256, 512] {
        let mut claims = OutcomeClaimGoals::open(
            (0..count).map(|index| (FunctionContractClaimKey::Ensure(index), None)),
            false,
        );
        for index in 0..count {
            claims = claims
                .close(
                    &FunctionContractClaimKey::Ensure(index),
                    receipt(),
                    &core.identity,
                )
                .unwrap();
        }
        for (fact_count, facts) in &fact_sets {
            let context = crate::kernel::ContractClosingContext::new(&execution);
            let original = context.open(0, &core);
            let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut closing = original.clone();
                for kind in ContractClosingGoal::ORDER {
                    closing = closing
                        .prove_goal(
                            kind,
                            &execution,
                            path,
                            &specification,
                            &core,
                            &claims,
                            facts,
                        )
                        .unwrap();
                }
                closing.completion(path).unwrap();
                closing
            });
            assert_eq!(closed.first_open_goal(), None);
            assert_eq!(
                original.first_open_goal(),
                Some(ContractClosingGoal::ReturnedResources)
            );
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{count} closed claims, {fact_count} unrelated facts"
            );
            assert!(
                work < 500,
                "empty boundary must stay a small primitive: {work}"
            );
        }
    }
}
