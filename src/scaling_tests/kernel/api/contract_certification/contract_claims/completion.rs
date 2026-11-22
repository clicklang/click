use super::*;

#[test]
fn whole_contract_retirement_is_indexed_and_preserves_candidate_forks() {
    for clauses in [16_usize, 64, 256, 512] {
        for unrelated in [0, 256] {
            let base = contract_closing_tests::fixture();
            let ensure = base.contract_ensures()[0].clone();
            let function = base.with_contract(
                (0..unrelated)
                    .map(|index| SpecProposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                        resource_state_dependent: false,
                    })
                    .collect(),
                vec![ensure; clauses],
                vec![],
                (0..clauses)
                    .map(|index| FunctionContractClaim::ensure_proposition(index, index))
                    .collect(),
                true,
            );
            let entry = prepare_function_contract_entry_cases(
                program_function_contract_entry(&ExecutionState::new(), &function, &[]).unwrap(),
                ExecutionEnvironment::new().byte_order_fact(),
            );
            let original = WholeContractProof::open(Arc::new(entry)).unwrap();
            let ((closed, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut candidate = original.clone();
                    for index in (0..clauses).rev() {
                        candidate.retire(ContractCompletionGoal::Claim {
                            case: 0,
                            key: FunctionContractClaimKey::Ensure(index),
                        });
                        assert_eq!(
                            candidate.first_open(),
                            Some(ContractCompletionGoal::Boundary { case: 0 })
                        );
                    }
                    candidate.retire(ContractCompletionGoal::Boundary { case: 0 });
                    candidate
                })
            });
            assert!(closed.first_open().is_none());
            assert_eq!(original.open.len(), clauses + 1);
            assert!(
                work <= 4 * clauses + 4,
                "{clauses} clauses, {unrelated} unrelated requirements: {work}"
            );
            assert!(
                indexed_work <= 32 * clauses * (clauses.ilog2() as usize + 1),
                "{clauses} clauses, {unrelated} unrelated requirements: {indexed_work} index visits"
            );
        }
    }
}

#[test]
fn ordinary_completion_visits_selected_goals_without_scanning_siblings() {
    for paths in [16_usize, 64, 256, 512] {
        for unrelated_claims in [0, 256] {
            let (owner, mut progress, goals) = fixture_with_claims(1, paths, unrelated_claims + 1);
            let original = progress.clone();
            let (((), work), indexed_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for goal in goals {
                        finish(&mut progress, goal).unwrap();
                    }
                })
            });
            assert_eq!(
                progress.closed.len(),
                2,
                "only the selected claim and boundary closed"
            );
            assert_eq!(progress.remaining.len(), unrelated_claims);
            assert!(original.closed.is_empty());
            assert_eq!(owner.open.len(), unrelated_claims + 2);
            assert!(
                work <= 40 * paths,
                "{paths} paths, {unrelated_claims} other claims: {work} work"
            );
            assert!(
                indexed_work <= 128 * paths * ((paths + unrelated_claims + 1).ilog2() as usize + 1),
                "{paths} paths, {unrelated_claims} other claims: {indexed_work} index visits"
            );
        }
    }
}

#[test]
fn selected_source_clause_completion_ignores_sibling_claims() {
    for size in [16_usize, 64, 256, 1024] {
        let (_, _, goals) = fixture_with_support(1, 1, size, false);
        let goal = source_goal(goals[0].clone(), size);
        let key = FunctionContractClaimKey::Ensure(size - 1);
        let ((closed, work), indexed) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let completion = source_completion(&goal, &key);
                goal.claims
                    .as_ref()
                    .unwrap()
                    .close(
                        &key,
                        ClaimGoalEvidence::Proposition(completion),
                        &goal.data.core.identity,
                    )
                    .unwrap()
            })
        });
        assert_eq!(closed.first_open_position(), Some(0));
        assert!(closed.evidence(&key).is_some());
        assert!(goal.claims.as_ref().unwrap().evidence(&key).is_none());
        assert!(work <= 64, "{size} sibling claims: {work} work");
        assert!(
            indexed <= 128 * (size.ilog2() as usize + 1),
            "{size} sibling claims: {indexed} index work"
        );
    }
}
