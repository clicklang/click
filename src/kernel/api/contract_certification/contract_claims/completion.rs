//! Ownership of the complete clause-by-entry-case contract judgment.

use super::*;
use crate::persistent::PersistentMap;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) enum ContractCompletionGoal {
    Boundary {
        case: usize,
    },
    Claim {
        case: usize,
        key: FunctionContractClaimKey,
    },
}

/// An unfinished contract, opened before body tactics. Candidate proof forks
/// share the plan and indexes; closing one cell never closes its siblings.
#[derive(Clone)]
pub(crate) struct WholeContractProof {
    entry: Arc<PreparedContractEntryCases>,
    open: PersistentMap<ContractCompletionGoal, ()>,
}

impl std::fmt::Debug for WholeContractProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WholeContractProof")
            .field("function", &self.entry.function.name())
            .field("unfinished", &self.open.len())
            .finish_non_exhaustive()
    }
}

/// Executions have been admitted to this owner's entry alternatives, but the
/// clause and boundary obligations remain ordinary open proof obligations.
#[derive(Clone)]
pub(crate) struct AdmittedContractProof {
    owner: WholeContractProof,
    function: ProgramFunction,
    execution: Arc<FunctionContractExecution>,
    claims: PersistentMap<FunctionContractClaimKey, VerifiedFunctionContractClaim>,
}

/// Evidence that every declared clause and every entry boundary was completed.
/// Registration receives an already packaged rule; it discovers no new claim
/// requirements and cannot substitute another function or a subset of proofs.
#[derive(Debug)]
pub(crate) struct CompletedContract {
    rule: Option<VerifiedFunctionRule>,
}

impl CompletedContract {
    pub(crate) fn into_rule(self) -> Option<VerifiedFunctionRule> {
        self.rule
    }
}

impl WholeContractProof {
    pub(crate) fn open(entry: Arc<PreparedContractEntryCases>) -> Result<Self, String> {
        let function = &entry.function;
        if entry.cases.is_empty()
            || function.contract_claims().is_empty()
            // Startup-owned effects are closed by the program-entry boundary;
            // program entry never produces a modular function rule.
            || (!function.is_program_entry()
                && (!function_contract_claims_are_complete(function)
                    || !function.verified_direct_contract_supported()))
        {
            return Err("the declaration does not describe a complete supported contract".into());
        }
        let mut keys = BTreeSet::new();
        for claim in function.contract_claims() {
            if !keys.insert(claim.key()) {
                return Err("the contract declaration reuses a claim identity".into());
            }
        }
        let mut open = PersistentMap::default();
        for case in 0..entry.cases.len() {
            crate::instrumentation::record_deterministic_work(1);
            open.insert(ContractCompletionGoal::Boundary { case }, ());
            for claim in function.contract_claims() {
                crate::instrumentation::record_deterministic_work(1);
                open.insert(
                    ContractCompletionGoal::Claim {
                        case,
                        key: claim.key().clone(),
                    },
                    (),
                );
            }
        }
        Ok(Self { entry, open })
    }

    pub(crate) fn admit_executions(
        self,
        function: ProgramFunction,
        environment: ExecutionEnvironment,
        semantics: ExecutionSemantics,
        mode: FunctionContractExecutionMode,
        artifacts: &[CheckedFunctionExecution],
        theorems: &[VerifiedPureTheorem],
    ) -> AdmittedContractProof {
        let execution =
            if !function.is_program_entry() && !function.verified_direct_contract_supported() {
                FunctionContractExecution::failed(
                    "the execution subject does not support a modular contract rule".into(),
                )
            } else {
                prove_prepared_function_contract_execution_paths(
                    &self.entry,
                    function.clone(),
                    environment,
                    semantics,
                    mode,
                    artifacts,
                    theorems,
                )
            };
        AdmittedContractProof {
            owner: self,
            function,
            execution: Arc::new(execution),
            claims: PersistentMap::default(),
        }
    }

    fn retire(&mut self, goal: ContractCompletionGoal) {
        crate::instrumentation::record_deterministic_work(1);
        self.open.remove(&goal);
    }

    fn first_open(&self) -> Option<ContractCompletionGoal> {
        crate::instrumentation::record_deterministic_work(1);
        self.open.keys().next().cloned()
    }
}

impl AdmittedContractProof {
    pub(crate) fn execution(&self) -> &Arc<FunctionContractExecution> {
        &self.execution
    }

    /// Consume checked closing receipts for these explicit executions. This
    /// replaces the old registration coverage walk; it never lowers a clause
    /// or runs a resource transition again.
    pub(crate) fn consume_completions(
        mut self,
        propositions: &[CheckedFunctionProposition],
    ) -> Self {
        let cases = contract_path_set_views(&self.execution, false);
        let checked = checked_proposition_index(propositions);
        for (case, alternatives) in self.execution.cases.iter().enumerate() {
            if closed_exit_obligations_cover_case(alternatives) {
                self.owner.retire(ContractCompletionGoal::Boundary { case });
            }
        }
        for claim in self.function.contract_claims() {
            if self.claims.get(claim.key()).is_some() {
                continue;
            }
            let capture = crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
                &self.execution.checked_call_events,
            );
            let operation = match claim.target() {
                FunctionContractClaimTarget::BodySafety => "contract claim: body safety",
                FunctionContractClaimTarget::EnsureProposition(_) => "contract claim: proposition",
                FunctionContractClaimTarget::ExceptionalEnsureProposition(_) => {
                    "contract claim: exceptional proposition"
                }
                FunctionContractClaimTarget::EnsureResource(_) => "contract claim: resource",
                FunctionContractClaimTarget::Effect => "contract claim: effect",
            };
            let complete = crate::instrumentation::measure_operation(
                self.function.name(),
                &format!("{:?}", claim.key()),
                operation,
                || {
                    let mut complete = !cases.is_empty();
                    for (case, alternatives) in cases.iter().enumerate() {
                        let goal = ContractCompletionGoal::Claim {
                            case,
                            key: claim.key().clone(),
                        };
                        if self.owner.open.get(&goal).is_none() {
                            continue;
                        }
                        let holds = if alternatives.is_empty() {
                            false
                        } else if is_proposition_claim(claim.target()) {
                            closed_proposition_holds_on_every_case(
                                claim.target(),
                                std::slice::from_ref(alternatives),
                                &checked,
                            )
                        } else {
                            closed_resource_effect_claim_holds(
                                claim,
                                std::slice::from_ref(alternatives),
                            )
                        };
                        if holds {
                            self.owner.retire(goal);
                        } else {
                            complete = false;
                        }
                    }
                    complete
                },
            );
            let load_equalities = capture.finish();
            if complete {
                self.claims.insert(
                    claim.key().clone(),
                    VerifiedFunctionContractClaim {
                        pointer_result: self.execution.pointer_result.clone(),
                        function: self.function.clone(),
                        key: claim.key().clone(),
                        load_equalities,
                        loop_semantics: self.execution.loop_semantics,
                        applied_tactics: self.execution.applied_tactics.clone(),
                        checked_callees: self.execution.checked_callees.clone(),
                    },
                );
            }
        }
        self
    }

    pub(crate) fn complete(self) -> Result<CompletedContract, ContractCompletionGoal> {
        if let Some(goal) = self.owner.first_open() {
            return Err(goal);
        }
        // Every cell was retired by its checked producer. Construct the rule
        // directly from the retained execution metadata, without validating
        // those completions or the declaration a second time.
        let rule = (!self.function.is_program_entry()).then(|| VerifiedFunctionRule {
            pointer_result: self.execution.pointer_result.clone(),
            function: self.function,
            loop_semantics: self.execution.loop_semantics,
            checked_callees: self.execution.checked_callees.clone(),
            applied_tactics: self.execution.applied_tactics.clone(),
        });
        Ok(CompletedContract { rule })
    }
}

#[cfg(test)]
mod tests {
    use super::super::contract_closing_tests;
    use super::*;

    fn fixture(
        case_count: usize,
        path_count: usize,
    ) -> (AdmittedContractProof, Vec<Vec<CheckedFunctionProposition>>) {
        let (function, mut execution) = contract_closing_tests::fixture(path_count);
        let state = ExecutionState::new();
        let mut entry = prepare_function_contract_entry_cases(
            program_function_contract_entry(&state, &function, &[]).unwrap(),
            ExecutionEnvironment::new().byte_order_fact(),
        )
        .unwrap();
        // Duplicate input contexts are harmless; distinct producer-owned path
        // sets let the fixture exercise case ownership without guard lowering.
        entry.cases = vec![entry.cases[0].clone(); case_count];
        entry.guard_cases = vec![vec![]; case_count];
        let owner = WholeContractProof::open(Arc::new(entry)).unwrap();
        let mut propositions = vec![contract_closing_tests::completions(&function, &execution)];
        for _ in 1..case_count {
            let (_, next) = contract_closing_tests::fixture(path_count);
            propositions.push(contract_closing_tests::completions(&function, &next));
            execution.cases.push(next.cases.into_iter().next().unwrap());
        }
        (
            AdmittedContractProof {
                owner,
                function,
                execution: Arc::new(execution),
                claims: PersistentMap::default(),
            },
            propositions,
        )
    }

    #[test]
    fn a_finished_clause_does_not_complete_another_entry_case_or_fork() {
        let (proof, propositions) = fixture(2, 1);
        let left = proof.clone().consume_completions(&propositions[0]);
        assert_eq!(
            left.clone().complete().unwrap_err(),
            ContractCompletionGoal::Claim {
                case: 1,
                key: FunctionContractClaimKey::Ensure(0),
            }
        );
        let right = proof.clone().consume_completions(&propositions[1]);
        assert_eq!(
            right.complete().unwrap_err(),
            ContractCompletionGoal::Claim {
                case: 0,
                key: FunctionContractClaimKey::Ensure(0),
            }
        );
        let completed = left
            .consume_completions(&propositions[1])
            .complete()
            .unwrap();
        assert!(completed.into_rule().is_some());
        assert_eq!(
            proof.owner.open.len(),
            4,
            "persistent ancestors retain all obligations"
        );
    }

    #[test]
    fn a_claim_requires_every_path_and_the_exact_producer_receipt() {
        let (proof, propositions) = fixture(1, 2);
        assert!(matches!(
            proof
                .clone()
                .consume_completions(&propositions[0][..1])
                .complete(),
            Err(ContractCompletionGoal::Claim { .. })
        ));
        let mut foreign = propositions[0].clone();
        let origin = foreign[1].path_origin.as_ref().unwrap();
        foreign[1].path_origin = Some(Theorem::new(origin.proposition().clone()));
        assert!(matches!(
            proof.clone().consume_completions(&foreign).complete(),
            Err(ContractCompletionGoal::Claim { .. })
        ));
        let mut wrong_clause = propositions[0].clone();
        wrong_clause[1].claim = Some(FunctionContractClaimTarget::EnsureProposition(1));
        assert!(
            proof
                .clone()
                .consume_completions(&wrong_clause)
                .complete()
                .is_err()
        );
        assert!(
            proof
                .consume_completions(&propositions[0])
                .complete()
                .unwrap()
                .into_rule()
                .is_some()
        );
    }

    #[test]
    fn all_propositions_without_the_boundary_completion_are_still_unfinished() {
        let (mut proof, propositions) = fixture(2, 1);
        Arc::make_mut(&mut proof.execution).cases[1][0]
            .closed_exit_obligations
            .clear();
        let all = propositions.into_iter().flatten().collect::<Vec<_>>();
        assert_eq!(
            proof.consume_completions(&all).complete().unwrap_err(),
            ContractCompletionGoal::Boundary { case: 1 }
        );
    }

    #[test]
    fn entry_cases_can_finish_using_different_execution_strategies() {
        let (mut proof, mut propositions) = fixture(2, 1);
        let (_, alternative) = contract_closing_tests::fixture(2);
        propositions[1] = contract_closing_tests::completions(&proof.function, &alternative);
        Arc::make_mut(&mut proof.execution).cases[1].push(alternative.cases[0][0].clone());
        let all = propositions.into_iter().flatten().collect::<Vec<_>>();
        assert!(
            proof
                .consume_completions(&all)
                .complete()
                .unwrap()
                .into_rule()
                .is_some()
        );
    }

    #[test]
    fn a_foreign_execution_subject_cannot_complete_the_owner() {
        let (proof, _) = fixture(1, 1);
        let other = program_function(
            ProgramType::Int32,
            "other",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let admitted = proof.owner.admit_executions(
            other,
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
            &[],
            &[],
        );
        assert!(admitted.consume_completions(&[]).complete().is_err());
    }

    mod scaling_tests {
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/completion.rs"
        );
    }
}
