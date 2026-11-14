#[test]
fn closing_evidence_work_tracks_paths_instead_of_ambient_facts() {
    let mut samples = Vec::new();
    for path_count in [1, 4, 16] {
        let mut costs = Vec::new();
        for fact_count in [0, 64, 1024] {
            let (function, mut execution) = fixture(path_count);
            let assumptions = (0..fact_count).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(971_000 + index)),
                        MachineTerm::constant(0),
                    ),
                    true,
                ))
            });
            for path in &mut execution.cases[0][0].paths {
                path.assumptions = assumptions.clone();
                let mut proposition = path.theorem.proposition().clone();
                for _ in 0..fact_count {
                    proposition = Proposition::Implies(
                        Box::new(Proposition::ConditionIs(
                            ConditionTerm::Constant(true),
                            true,
                        )),
                        Box::new(proposition),
                    );
                }
                path.theorem = Theorem::new(proposition);
            }
            execution.cases[0][0].completion_path_origins = execution.cases[0][0]
                .paths
                .iter()
                .map(|path| path.theorem.clone())
                .collect();
            let proofs = completions(&function, &execution);
            let cases = contract_path_set_views(&execution, false);
            let index = checked_proposition_index(&proofs);
            let (closed, work) = crate::instrumentation::measure_deterministic_work(|| {
                closed_proposition_holds_on_every_case(
                    &CFunctionContractClaimTarget::EnsureProposition(0),
                    &cases,
                    &index,
                )
            });
            assert!(closed);
            assert!(
                cases
                    .iter()
                    .flatten()
                    .all(|view| view.prepared.get().is_none())
            );
            let missing = CheckedPropositionIndex::default();
            let (closed, miss_work) = crate::instrumentation::measure_deterministic_work(|| {
                closed_proposition_holds_on_every_case(
                    &CFunctionContractClaimTarget::EnsureProposition(0),
                    &cases,
                    &missing,
                )
            });
            assert!(!closed);
            assert_eq!(miss_work, 2);
            costs.push(work);
            // A completed context can refute a retained candidate even when
            // its entry assumptions are consistent. No closing goal is owed.
            let condition = ConditionTerm::equal(
                MachineTerm::Variable(Variable(973_000)),
                MachineTerm::constant(0),
            );
            let impossible = assumptions
                .clone()
                .assume_condition(condition.clone(), true)
                .assume_condition(condition, false);
            for path in &mut execution.cases[0][0].paths {
                path.post_assumptions = Some(impossible.clone());
            }
            let cases = contract_path_set_views(&execution, false);
            let (closed, vacuous_work) = crate::instrumentation::measure_deterministic_work(|| {
                closed_proposition_holds_on_every_case(
                    &CFunctionContractClaimTarget::EnsureProposition(0),
                    &cases,
                    &missing,
                )
            });
            assert!(closed);
            assert_eq!(vacuous_work, path_count);
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
        samples.push((path_count, costs[0]));
    }
    assert_eq!(samples, vec![(1, 2), (4, 8), (16, 32)]);
}

#[test]
fn resource_and_effect_completion_lookup_ignores_unrelated_path_history() {
    let resource = CFunctionContractClaim::ensure_resource(0, 0);
    let effect = CFunctionContractClaim::effect(0);
    for paths in [1, 4, 16] {
        let mut costs = Vec::new();
        for facts in [0, 64, 1024] {
            let (_, mut execution) = fixture(paths);
            let assumptions = (0..facts).fold(PureFactContext::new(), |context, index| {
                context.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(975_000 + index)),
                        MachineTerm::constant(0),
                    ),
                    true,
                )
            });
            for path in &mut execution.cases[0][0].paths {
                path.post_assumptions = Some(assumptions.clone());
            }
            execution.cases[0][0].closed_exit_obligations = execution.cases[0][0]
                .paths
                .iter()
                .enumerate()
                .map(|(index, path)| {
                    Some(CClosedContractExit::fixture_for_claims(
                        index,
                        path,
                        [resource.key().clone()],
                    ))
                })
                .collect();
            let cases = contract_path_set_views(&execution, false);
            let ((resource_closed, effect_closed), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    (
                        closed_resource_effect_claim_holds(&resource, &cases),
                        closed_resource_effect_claim_holds(&effect, &cases),
                    )
                });
            assert!(resource_closed && effect_closed);
            assert!(
                cases
                    .iter()
                    .flatten()
                    .all(|view| view.prepared.get().is_none())
            );
            costs.push(work);
            let wrong = CFunctionContractClaim::ensure_resource(1, 1);
            assert!(!closed_resource_effect_claim_holds(&wrong, &cases));
            execution.cases[0][0].closed_exit_obligations.clear();
            assert!(!closed_exit_obligations_cover_every_case(&execution));
        }
        assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
        assert_eq!(costs[0], paths * 4);
    }
}
