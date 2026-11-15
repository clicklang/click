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
        artifacts: &[CheckedFunctionExecution],
    ) -> AdmittedContractProof {
        // The entry owns the declaration; its execution producer also retains
        // proof-only body annotations (including normalized natural loops).
        // Select that bound subject rather than stripping those annotations.
        let function = artifacts
            .iter()
            .find(|artifact| {
                crate::instrumentation::record_deterministic_work(1);
                artifact
                    .entry_authority
                    .as_ref()
                    .is_some_and(|authority| Arc::ptr_eq(authority.cases(), &self.entry))
            })
            .map_or_else(
                || self.entry.function.clone(),
                |artifact| artifact.function.clone(),
            );
        let execution = execution_from_owned_contract_entry(&self.entry, artifacts);
        let mut owner = self;
        for artifact in artifacts {
            if let Some(progress) = &artifact.contract_completion {
                owner.accept_progress(progress);
            }
        }
        AdmittedContractProof {
            owner,
            function,
            execution: Arc::new(execution),
        }
    }

    fn accept_progress(&mut self, progress: &ContractProofProgress) {
        if !Arc::ptr_eq(&self.entry, &progress.owner.entry) {
            return;
        }
        // These are explicit outputs of ordinary proof completion, not
        // receipts from which registration has to infer path coverage.
        for goal in progress.closed.keys() {
            self.retire(goal.clone());
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

/// One execution strategy's persistent contribution to its whole-contract
/// owner. Counts are per declared obligation, never combined across strategies.
#[derive(Clone)]
pub(crate) struct ContractProofProgress {
    identity: Arc<()>,
    strategy: Option<FunctionExecutionCandidates>,
    owner: WholeContractProof,
    outcomes: PersistentMap<usize, (crate::kernel::proof::OutcomeIdentity, bool)>,
    remaining: PersistentMap<ContractPathGoal, (usize, &'static str)>,
    closed: PersistentMap<ContractCompletionGoal, ()>,
}

impl std::fmt::Debug for ContractProofProgress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContractProofProgress")
            .field("function", &self.owner.entry.function.name())
            .field("remaining", &self.remaining.len())
            .field("closed", &self.closed.len())
            .finish_non_exhaustive()
    }
}
impl PartialEq for ContractProofProgress {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.identity, &other.identity)
    }
}
impl Eq for ContractProofProgress {}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
enum ContractPathGoal {
    Boundary,
    Claim(FunctionContractClaimKey),
}

impl ContractProofProgress {
    pub(in crate::kernel) fn open(
        owner: &WholeContractProof,
        execution: &CheckedFunctionExecution,
        outcomes: impl Iterator<Item = (usize, crate::kernel::proof::OutcomeIdentity)>,
    ) -> Option<Self> {
        let authority = execution.entry_authority.as_ref()?;
        if !Arc::ptr_eq(authority.cases(), &owner.entry) || execution.paths().is_empty() {
            return None;
        }
        let mut remaining_paths = 0;
        for path in execution.paths() {
            crate::instrumentation::record_deterministic_work(1);
            if !closing_path_is_unreachable(path) {
                remaining_paths += 1;
            }
        }
        let mut progress = Self {
            identity: Arc::new(()),
            strategy: Some(execution.proof_candidates.as_ref()?.clone()),
            owner: owner.clone(),
            outcomes: outcomes
                .filter_map(|(index, identity)| {
                    execution
                        .paths()
                        .get(index)
                        .map(|path| (index, (identity, !closing_path_is_unreachable(path))))
                })
                .collect(),
            remaining: PersistentMap::default(),
            closed: PersistentMap::default(),
        };
        progress.open_goal(
            ContractPathGoal::Boundary,
            remaining_paths,
            "contract boundary",
        );
        for claim in execution.function.contract_claims() {
            let operation = match claim.target() {
                FunctionContractClaimTarget::BodySafety => "contract claim: body safety",
                FunctionContractClaimTarget::EnsureProposition(_) => "contract claim: proposition",
                FunctionContractClaimTarget::ExceptionalEnsureProposition(_) => {
                    "contract claim: exceptional proposition"
                }
                FunctionContractClaimTarget::EnsureResource(_) => "contract claim: resource",
                FunctionContractClaimTarget::Effect => "contract claim: effect",
            };
            progress.open_goal(
                ContractPathGoal::Claim(claim.key().clone()),
                remaining_paths,
                operation,
            );
        }
        Some(progress)
    }

    pub(in crate::kernel) fn belongs_to(&self, execution: &CheckedFunctionExecution) -> bool {
        self.strategy
            .as_ref()
            .zip(execution.proof_candidates.as_ref())
            .is_some_and(|(left, right)| Arc::ptr_eq(&left.data, &right.data))
            && execution
                .entry_authority
                .as_ref()
                .is_some_and(|authority| Arc::ptr_eq(authority.cases(), &self.owner.entry))
    }

    fn open_goal(&mut self, goal: ContractPathGoal, paths: usize, operation: &'static str) {
        crate::instrumentation::record_deterministic_work(1);
        if paths == 0 {
            self.retire(goal);
        } else {
            self.remaining.insert(goal, (paths, operation));
        }
    }

    fn retire(&mut self, goal: ContractPathGoal) {
        self.remaining.remove(&goal);
        for case in 0..self.owner.entry.cases.len() {
            crate::instrumentation::record_deterministic_work(1);
            let closed = match &goal {
                ContractPathGoal::Boundary => ContractCompletionGoal::Boundary { case },
                ContractPathGoal::Claim(key) => ContractCompletionGoal::Claim {
                    case,
                    key: key.clone(),
                },
            };
            self.owner.retire(closed.clone());
            self.closed.insert(closed, ());
        }
    }

    fn finish_goal(&mut self, goal: ContractPathGoal) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(&(paths, operation)) = self.remaining.get(&goal) else {
            return;
        };
        let entry = self.owner.entry.clone();
        crate::instrumentation::measure_operation(entry.function.name(), "", operation, || {
            crate::instrumentation::record_deterministic_work(1);
            if paths == 1 {
                self.retire(goal);
            } else {
                self.remaining.insert(goal, (paths - 1, operation));
            }
        });
    }

    /// Called by the ordinary outcome-completion operation. The generative
    /// identity selects the outcome opened for this strategy, preventing a
    /// sibling strategy or a replay from contributing another path's proof.
    pub(in crate::kernel) fn finish_outcome(
        &self,
        path: usize,
        identity: &crate::kernel::proof::OutcomeIdentity,
        claims: Option<&crate::kernel::proof::OutcomeClaimGoals>,
        closing: Option<&ContractExitObligations>,
    ) -> Result<Self, String> {
        crate::instrumentation::record_deterministic_work(1);
        let Some((owned, contributes)) = self.outcomes.get(&path) else {
            return Err("the contract outcome was not opened or was already consumed".into());
        };
        if !owned.same_as(identity) {
            return Err("the completion belongs to another contract outcome".into());
        }
        let mut next = self.clone();
        next.identity = Arc::new(());
        next.outcomes.remove(&path);
        // An already unreachable producer path owes no counter decrement.
        // It cannot stand in for a still-live sibling path.
        if !contributes {
            return Ok(next);
        }
        match (claims, closing) {
            (Some(claims), Some(closing)) => {
                for key in claims
                    .completed_proposition_keys()
                    .chain(closing.completed_claim_keys())
                {
                    next.finish_goal(ContractPathGoal::Claim(key.clone()));
                }
                if closing.completes_whole_boundary() {
                    next.finish_goal(ContractPathGoal::Boundary);
                }
            }
            // A checked refutation discharges every obligation on this path.
            (None, None) => {
                let goals = self.remaining.keys().cloned().collect::<Vec<_>>();
                for goal in goals {
                    next.finish_goal(goal);
                }
            }
            _ => unreachable!("a completed outcome owns both source and closing goals"),
        }
        Ok(next)
    }
}

#[cfg(test)]
mod tests {
    use super::super::contract_closing_tests;
    use super::*;
    use crate::kernel::proof::*;

    type Goal = FunctionOutcomeObligation<Arc<OutcomeProofState<()>>>;
    type Root =
        ProofObject<(), crate::kernel::proof::ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;

    fn root(goal: Goal) -> Root {
        ProofObject::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::FunctionOutcome(goal),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(&[]),
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        )
    }

    fn fixture(
        case_count: usize,
        path_count: usize,
    ) -> (WholeContractProof, ContractProofProgress, Vec<Goal>) {
        fixture_with_claims(case_count, path_count, 1)
    }

    fn fixture_with_claims(
        case_count: usize,
        path_count: usize,
        claim_count: usize,
    ) -> (WholeContractProof, ContractProofProgress, Vec<Goal>) {
        let (base, _) = contract_closing_tests::fixture(path_count);
        let ensure = base.contract_ensures()[0].clone();
        let function = base.with_contract(
            vec![],
            vec![ensure; claim_count],
            vec![],
            (0..claim_count)
                .map(|index| FunctionContractClaim::ensure_proposition(index, index))
                .collect(),
            true,
        );
        let mut entry = prepare_function_contract_entry_cases(
            program_function_contract_entry(&ExecutionState::new(), &function, &[]).unwrap(),
            ExecutionEnvironment::new().byte_order_fact(),
        )
        .unwrap();
        entry.cases = vec![entry.cases[0].clone(); case_count];
        entry.guard_cases = vec![vec![]; case_count];
        let owner = WholeContractProof::open(Arc::new(entry)).unwrap();
        let execution = prove_checked_program_function_execution_with_environment(
            ExecutionState::new(),
            function.clone(),
            vec![],
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        );
        let context = ContractClosingContext::new(&execution);
        let goals = (0..path_count)
            .map(|path_index| {
                let core = OutcomeProofCore {
                    identity: OutcomeIdentity::fresh(),
                    store_consequences_available: false,
                    result: Arc::new(int32(0)),
                    state: ExecutionState::new().into(),
                    // Normal postconditions hold vacuously on a throwing path.
                    // The ordinary outcome operation still owes all closing goals.
                    is_exceptional: true,
                    effect_facts: ExecutionFacts::new().into(),
                };
                let mut closing = context.open(path_index, &core);
                for kind in [
                    ContractClosingGoal::ReturnedResources,
                    ContractClosingGoal::AllocationLifetime,
                    ContractClosingGoal::WriteFootprint,
                ] {
                    closing = closing.fixture_close_goal(kind);
                }
                let mut goal = Goal::new(path_index, Arc::new(OutcomeProofState::new(core, ())));
                goal.claims = Some(OutcomeClaimGoals::open(
                    function
                        .contract_claims()
                        .iter()
                        .take(1)
                        .map(|claim| (claim.key().clone(), Some(claim.target().clone()))),
                    true,
                ));
                goal.closing = Some(closing);
                goal
            })
            .collect::<Vec<_>>();
        let mut progress = ContractProofProgress {
            identity: Arc::new(()),
            strategy: None,
            owner: owner.clone(),
            outcomes: goals
                .iter()
                .map(|goal| (goal.path_index, (goal.data.core.identity.clone(), true)))
                .collect(),
            remaining: PersistentMap::default(),
            closed: PersistentMap::default(),
        };
        progress.open_goal(ContractPathGoal::Boundary, path_count, "contract boundary");
        for index in 0..claim_count {
            progress.open_goal(
                ContractPathGoal::Claim(FunctionContractClaimKey::Ensure(index)),
                path_count,
                "contract claim: proposition",
            );
        }
        (owner, progress, goals)
    }

    fn finish(progress: &mut ContractProofProgress, goal: Goal) -> Result<(), String> {
        let proof = root(goal);
        assert!(
            proof
                .complete_function_outcome_with_contract_in(&proof, Some(progress))?
                .is_complete()
        );
        Ok(())
    }

    #[test]
    fn ordinary_outcome_completion_retires_the_whole_contract_directly() {
        let (mut owner, mut progress, goals) = fixture(2, 2);
        let original = progress.clone();
        finish(&mut progress, goals[0].clone()).unwrap();
        owner.accept_progress(&progress);
        assert_eq!(owner.open.len(), 4, "a sibling path is still open");
        finish(&mut progress, goals[1].clone()).unwrap();
        assert_eq!(
            progress.closed.len(),
            4,
            "completion already retired every entry case"
        );
        assert!(progress.owner.first_open().is_none());
        owner.accept_progress(&progress);
        assert!(owner.first_open().is_none());
        assert!(
            original.closed.is_empty(),
            "proof forks retain their open obligations"
        );
    }

    #[test]
    fn an_already_unreachable_outcome_cannot_decrement_a_live_sibling() {
        let (_, mut progress, goals) = fixture(1, 2);
        progress
            .outcomes
            .insert(0, (goals[0].data.core.identity.clone(), false));
        // Only path 1 contributes to the counters: path 0 was already refuted
        // when the strategy opened, and cannot discharge that live path.
        for goal in [
            ContractPathGoal::Boundary,
            ContractPathGoal::Claim(FunctionContractClaimKey::Ensure(0)),
        ] {
            let operation = progress.remaining.get(&goal).unwrap().1;
            progress.remaining.insert(goal, (1, operation));
        }
        finish(&mut progress, goals[0].clone()).unwrap();
        assert!(progress.closed.is_empty());
        finish(&mut progress, goals[1].clone()).unwrap();
        assert!(progress.owner.first_open().is_none());
    }

    #[test]
    fn partial_execution_strategies_cannot_complete_each_other() {
        let (mut owner, mut left, goals) = fixture(1, 2);
        let mut right = left.clone();
        finish(&mut left, goals[0].clone()).unwrap();
        finish(&mut right, goals[1].clone()).unwrap();
        owner.accept_progress(&left);
        owner.accept_progress(&right);
        assert_eq!(owner.open.len(), 2);
        finish(&mut left, goals[1].clone()).unwrap();
        owner.accept_progress(&left);
        assert!(owner.first_open().is_none());
    }

    #[test]
    fn foreign_outcomes_replays_and_entry_owners_cannot_supply_progress() {
        let (mut owner, mut progress, goals) = fixture(1, 1);
        let (_, mut foreign_progress, foreign_goals) = fixture(1, 1);
        assert!(finish(&mut progress, foreign_goals[0].clone()).is_err());
        finish(&mut foreign_progress, foreign_goals[0].clone()).unwrap();
        owner.accept_progress(&foreign_progress);
        assert_eq!(owner.open.len(), 2);
        finish(&mut progress, goals[0].clone()).unwrap();
        assert!(finish(&mut progress, goals[0].clone()).is_err());
        owner.accept_progress(&progress);
        assert!(owner.first_open().is_none());
    }

    #[test]
    fn unfinished_closing_or_source_goals_cannot_update_the_whole_owner() {
        let (owner, mut progress, mut goals) = fixture(1, 1);
        let mut goal = goals.pop().unwrap();
        let closed = goal.closing.take().unwrap();
        assert!(finish(&mut progress, goal.clone()).is_err());
        assert!(progress.closed.is_empty());
        goal.closing = Some(closed);
        goal.claims = Some(OutcomeClaimGoals::open(
            [(
                FunctionContractClaimKey::Ensure(0),
                Some(FunctionContractClaimTarget::EnsureProposition(0)),
            )],
            false,
        ));
        assert!(finish(&mut progress, goal).is_err());
        assert!(progress.closed.is_empty());
        assert_eq!(owner.open.len(), 2);
    }

    #[test]
    fn registration_consumes_ordinary_completion_without_scanning_receipts() {
        let (entry, execution) =
            super::super::super::entry_authority_tests::checked_execution(0, None).unwrap();
        let owner = WholeContractProof::open(entry).unwrap();
        let core = OutcomeProofCore {
            identity: OutcomeIdentity::fresh(),
            store_consequences_available: false,
            result: Arc::new(ProgramValue::Void),
            state: ExecutionState::new().into(),
            is_exceptional: false,
            effect_facts: ExecutionFacts::new().into(),
        };
        let context = ContractClosingContext::new(&execution);
        let mut closing = context.open(0, &core);
        for kind in [
            ContractClosingGoal::ReturnedResources,
            ContractClosingGoal::AllocationLifetime,
            ContractClosingGoal::WriteFootprint,
        ] {
            closing = closing.fixture_close_goal(kind);
        }
        let mut goal = Goal::new(0, Arc::new(OutcomeProofState::new(core, ())));
        goal.claims = Some(OutcomeClaimGoals::open([], false));
        goal.closing = Some(closing);
        let proof = root(goal);
        let mut progress = proof
            .start_contract_completion(&owner, &execution, std::iter::once(proof.focused_branch()))
            .unwrap();
        assert!(
            owner
                .clone()
                .admit_executions(std::slice::from_ref(&execution))
                .complete()
                .is_err()
        );
        let independent = prove_checked_program_function_execution_with_environment(
            execution.state.clone(),
            execution.function.clone(),
            vec![],
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        );
        assert!(
            proof
                .start_contract_completion(
                    &owner,
                    &independent,
                    std::iter::once(proof.focused_branch())
                )
                .is_none()
        );
        proof
            .complete_function_outcome_with_contract_in(&proof, Some(&mut progress))
            .unwrap();
        let mut wrong_strategy = execution.clone();
        wrong_strategy.proof_candidates =
            Some(program_function_execution_candidates_from_outcomes(
                execution.state.clone(),
                execution.function.clone(),
                vec![],
                vec![(FunctionOutcome::VerificationDiverges, vec![], vec![])],
            ));
        assert!(
            wrong_strategy
                .with_contract_completion(Some(progress.clone()))
                .contract_completion
                .is_none(),
            "a different strategy cannot publish this progress"
        );
        let completed_execution = execution.with_contract_completion(Some(progress));
        assert!(
            completed_execution
                .closed_exit_obligations
                .iter()
                .all(Option::is_none),
            "legacy path receipts were never published"
        );
        assert!(
            owner
                .admit_executions(&[completed_execution])
                .complete()
                .unwrap()
                .into_rule()
                .is_some()
        );
    }

    #[test]
    fn checked_refutation_retires_its_outcome_without_claim_receipts() {
        let (mut owner, mut progress, mut goals) = fixture(1, 1);
        let mut goal = goals.pop().unwrap();
        goal.claims = None;
        goal.closing = None;
        let proof = root(goal.clone());
        let contradiction =
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        assert!(
            proof
                .refute_function_outcome_with_contract_in(
                    &proof,
                    &contradiction,
                    Some(&mut progress)
                )
                .is_err()
        );
        assert!(progress.closed.is_empty());
        let routed = proof
            .replace_focused_obligation_and_facts(
                crate::kernel::proof::ProofObligation::FunctionOutcome(goal),
                ProofFacts::from_ordered(std::slice::from_ref(&contradiction)),
            )
            .unwrap_or_else(|_| panic!("the outcome is open"));
        routed
            .refute_function_outcome_with_contract_in(&proof, &contradiction, Some(&mut progress))
            .unwrap();
        owner.accept_progress(&progress);
        assert!(owner.first_open().is_none());
    }

    #[test]
    fn missing_execution_authority_cannot_complete_the_owner() {
        let (owner, _, _) = fixture(1, 1);
        assert!(owner.admit_executions(&[]).complete().is_err());
    }

    mod scaling_tests {
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/completion.rs"
        );
    }
}
