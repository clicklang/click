//! Ownership of the complete clause-by-entry-case contract judgment.

use super::*;
use crate::kernel::proof::{BranchId, ProofBranch, ProofBranchState, ProofFacts, ProofObject};
use crate::persistent::PersistentMap;
mod root;
pub(crate) use root::{CompletedContractExecution, WholeContractRoot};
#[derive(Clone)]
enum ContractRootObligation {
    WholeContract,
    Cell(ContractCompletionGoal),
}
type RootProof = ProofObject<Arc<PreparedContractEntryCases>, ContractRootObligation, ()>;

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
    open: PersistentMap<ContractCompletionGoal, BranchId>,
    proof: RootProof,
    modular: bool,
    loop_exits: Arc<crate::kernel::termination::loop_evidence::PreparedLoopExits>,
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
#[cfg(test)]
#[derive(Clone)]
pub(crate) struct AdmittedContractProof {
    owner: WholeContractProof,
    function: ProgramFunction,
    execution: Arc<FunctionContractExecution>,
}

/// Partial-correctness proof of every declared clause and entry boundary.
/// Eligible rules are usable during modular proof execution. Whole-contract
/// completion also needs the enclosing program's termination obligations.
#[derive(Clone, Debug)]
pub(crate) struct ContractBodyProof {
    rule: VerifiedFunctionRule,
    modular: bool,
    loop_rules: Vec<VerifiedLoopRule>,
}

/// Affine owner of one strategy's execution and ordinary outcome completions.
/// Successors are installed during completion, never by a later receipt pass.
pub(crate) struct ContractExecutionOwner {
    execution: CheckedFunctionExecution,
    progress: Option<ContractProofProgress>,
    open: PersistentMap<usize, crate::kernel::proof::OutcomeIdentity>,
    root: Option<WholeContractRoot>,
}

impl ContractExecutionOwner {
    pub(in crate::kernel) fn open(
        execution: CheckedFunctionExecution,
        whole: Option<&WholeContractProof>,
        outcomes: Vec<(
            usize,
            crate::kernel::proof::OutcomeIdentity,
            Arc<PublishedFunctionOutcome>,
        )>,
    ) -> Result<Self, String> {
        for (index, _, publication) in &outcomes {
            if !execution
                .published_outcomes
                .get(*index)
                .is_some_and(|original| publication.belongs_to(original))
            {
                return Err("outcome opening belongs to another execution producer".into());
            }
        }
        let progress = whole
            .map(|whole| {
                ContractProofProgress::open(
                    whole,
                    &execution,
                    outcomes
                        .iter()
                        .map(|(index, identity, _)| (*index, identity.clone())),
                )
                .ok_or_else(|| {
                    "execution opening belongs to another whole-contract entry".to_string()
                })
            })
            .transpose()?;
        Ok(Self {
            execution,
            progress,
            root: None,
            open: outcomes
                .into_iter()
                .map(|(index, identity, _)| (index, identity))
                .collect(),
        })
    }

    pub(in crate::kernel) fn finish_outcome(
        &mut self,
        index: usize,
        identity: &crate::kernel::proof::OutcomeIdentity,
        claims: Option<&crate::kernel::proof::OutcomeClaimGoals>,
        closing: Option<&ContractExitObligations>,
        publication: Option<&Arc<PublishedFunctionOutcome>>,
    ) -> Result<(), String> {
        if !self
            .open
            .get(&index)
            .is_some_and(|opened| opened.same_as(identity))
        {
            return Err(
                "completion belongs to another execution outcome or was already consumed".into(),
            );
        }
        let progress = self
            .progress
            .as_ref()
            .map(|progress| progress.finish_outcome(index, identity, claims, closing))
            .transpose()?;
        if let (Some(closing), Some(publication)) = (closing, publication) {
            let exit = closing.completed_exit(publication.path());
            self.execution.execution.paths[index] = publication.path().clone();
            self.execution.published_outcomes[index] = publication.clone();
            if let Some((deferred, error)) = publication.return_status() {
                self.execution.deferred_contract_exits[index] = *deferred;
                self.execution.deferred_contract_exit_errors[index] = error.clone();
            }
            self.execution.checked_resource_transitions[index] = exit.completes_boundary();
            self.execution.closed_exit_obligations[index] = Some(exit);
        }
        self.progress = progress;
        self.open.remove(&index);
        Ok(())
    }

    pub(in crate::kernel) fn bind_root(mut self, root: Option<&WholeContractRoot>) -> Self {
        self.root = root.cloned();
        self
    }

    pub(in crate::kernel) fn finish(mut self) -> Result<CompletedContractExecution, String> {
        if !self.open.is_empty() {
            return Err("execution still owns unfinished outcome obligations".into());
        }
        self.execution.contract_completion = self.progress.map(Arc::new);
        Ok(CompletedContractExecution::new(self.execution, self.root))
    }
}

impl ContractBodyProof {
    pub(crate) fn loop_rules(&self) -> &[VerifiedLoopRule] {
        &self.loop_rules
    }
    pub(crate) fn into_rule(&self) -> Option<VerifiedFunctionRule> {
        self.modular.then(|| self.rule.clone())
    }
    pub(in crate::kernel) fn termination_rule(&self) -> &VerifiedFunctionRule {
        &self.rule
    }
}

impl WholeContractProof {
    pub(crate) fn open(entry: Arc<PreparedContractEntryCases>) -> Result<Self, String> {
        let function = &entry.function;
        let loop_exits =
            crate::kernel::termination::loop_evidence::PreparedLoopExits::open(function)?;
        if entry.cases.is_empty() {
            return Err("the contract entry has no cases".into());
        }
        // Fix reusable-rule eligibility at opening. A startup or a contract
        // with source-only clauses still owns its body/termination proof, but
        // completing it must not expose an unsupported modular contract.
        let reusable_claims = function.opaque_contract_supported()
            && !function.contract_claims().is_empty()
            && (function.is_program_entry()
                || (function_contract_claims_are_complete(function)
                    && function.verified_direct_contract_supported()));
        let modular = reusable_claims && !function.is_program_entry();
        let mut keys = BTreeSet::new();
        for claim in function.contract_claims() {
            if !keys.insert(claim.key()) {
                return Err("the contract declaration reuses a claim identity".into());
            }
        }
        let mut goals = Vec::new();
        for case in 0..entry.cases.len() {
            crate::instrumentation::record_deterministic_work(1);
            goals.push(ContractCompletionGoal::Boundary { case });
            for claim in function.contract_claims() {
                crate::instrumentation::record_deterministic_work(1);
                goals.push(ContractCompletionGoal::Claim {
                    case,
                    key: claim.key().clone(),
                });
            }
        }
        let branch = |goal| {
            ProofBranch::new(
                goal,
                ProofBranchState {
                    facts: ProofFacts::default(),
                    execution: None,
                },
            )
        };
        let root = RootProof::root(entry.clone(), branch(ContractRootObligation::WholeContract));
        let (proof, ids) = root
            .replace_focused_with_checked_branches(
                goals
                    .iter()
                    .cloned()
                    .map(|goal| branch(ContractRootObligation::Cell(goal)))
                    .collect(),
            )
            .unwrap_or_else(|_| panic!("the contract root was just opened"));
        let open = goals.into_iter().zip(ids).collect();
        Ok(Self {
            entry,
            open,
            proof,
            modular,
            loop_exits,
        })
    }

    #[cfg(test)]
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

    #[cfg(test)]
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

    fn retire(&mut self, goal: ContractCompletionGoal) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        let Some(&branch) = self.open.get(&goal) else {
            return false;
        };
        self.proof = self
            .proof
            .focus_open_branch(branch)
            .unwrap_or_else(|_| panic!("the contract goal index addresses its open branch"))
            .publish_checked_focused_result(self.entry.clone(), None, vec![], vec![])
            .unwrap_or_else(|_| panic!("the selected contract goal is open"));
        self.open.remove(&goal);
        true
    }

    fn first_open(&self) -> Option<ContractCompletionGoal> {
        crate::instrumentation::record_deterministic_work(1);
        let id = self.open.values().next()?;
        match &self
            .proof
            .state()
            .open_branches()
            .get(*id)
            .expect("an indexed contract cell is open")
            .obligation
        {
            ContractRootObligation::Cell(goal) => Some(goal.clone()),
            ContractRootObligation::WholeContract => {
                unreachable!("the root was opened into its declared cells")
            }
        }
    }
}

#[cfg(test)]
impl AdmittedContractProof {
    pub(crate) fn execution(&self) -> &Arc<FunctionContractExecution> {
        &self.execution
    }

    pub(crate) fn complete(self) -> Result<ContractBodyProof, ContractCompletionGoal> {
        if let Some(goal) = self.owner.first_open() {
            return Err(goal);
        }
        // Every cell was retired by its checked producer. Construct the rule
        // directly from the retained execution metadata, without validating
        // those completions or the declaration a second time.
        let rule = VerifiedFunctionRule {
            pointer_result: self.execution.pointer_result.clone(),
            function: self.function,
            concrete_loop_exits: Some(self.owner.loop_exits.unknown()),
            loop_semantics: self.execution.loop_semantics,
            checked_callees: self.execution.checked_callees.clone(),
            applied_tactics: self.execution.applied_tactics.clone(),
        };
        Ok(ContractBodyProof {
            rule,
            modular: self.owner.modular,
            loop_rules: Vec::new(),
        })
    }
}

/// One execution strategy's persistent contribution to its whole-contract
/// owner. Counts are per declared obligation, never combined across strategies.
#[derive(Clone)]
pub(crate) struct ContractProofProgress {
    identity: Arc<()>,
    #[cfg(test)]
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
        let _strategy = execution.proof_candidates.as_ref()?;
        let mut progress = Self {
            identity: Arc::new(()),
            #[cfg(test)]
            strategy: Some(_strategy.clone()),
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
        let claims = owner.entry.function.contract_claims();
        for claim in claims {
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

    #[cfg(test)]
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
                    .completed_outcome_claim_keys()
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
        fixture_with_support(case_count, path_count, claim_count, true)
    }

    fn fixture_with_support(
        case_count: usize,
        path_count: usize,
        claim_count: usize,
        modular: bool,
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
            modular,
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
                    publication: None,
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

    fn source_completion(goal: &Goal, key: &FunctionContractClaimKey) -> CheckedProposition {
        let fact = Proposition::Predicate {
            name: "source_clause".into(),
            arguments: vec![],
        };
        let proof: Root = ProofObject::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::FunctionOutcome(goal.clone()),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(std::slice::from_ref(&fact)),
                    execution: None,
                },
            ),
        );
        proof
            .focus_source_contract_claim(key, fact, ())
            .unwrap()
            .apply_known(PropositionKnownContext::Exact)
            .unwrap_or_else(|_| panic!("the selected source clause is an exact root fact"))
            .completed_proposition()
            .unwrap()
    }

    fn source_goal(mut goal: Goal, count: usize) -> Goal {
        let mut core = goal.data.core.clone();
        core.is_exceptional = false;
        goal.data = Arc::new(OutcomeProofState::new(core, ()));
        goal.claims = Some(OutcomeClaimGoals::open(
            (0..count).map(|i| (FunctionContractClaimKey::Ensure(i), None)),
            false,
        ));
        goal
    }

    #[test]
    fn nonmodular_boundary_completion_cannot_skip_source_claim_cells() {
        let (mut owner, mut progress, goals) = fixture_with_support(2, 2, 2, false);
        assert!(!owner.modular);
        assert_eq!(owner.open.len(), 6);
        for mut goal in goals {
            goal.claims = Some(OutcomeClaimGoals::open([], false));
            finish(&mut progress, goal).unwrap();
        }
        owner.accept_progress(&progress);
        assert_eq!(
            owner.open.len(),
            4,
            "boundary proof does not imply source-clause proofs"
        );
        assert!(matches!(
            owner.first_open(),
            Some(ContractCompletionGoal::Claim { .. })
        ));
    }

    #[test]
    fn source_clause_proofs_retire_all_entry_cells_without_modular_reuse() {
        let (mut owner, mut progress, goals) = fixture_with_support(2, 2, 2, false);
        let untouched = progress.clone();
        for (path, goal) in goals.into_iter().enumerate() {
            let mut goal = source_goal(goal, 2);
            for i in 0..2 {
                let key = FunctionContractClaimKey::Ensure(i);
                let completion = source_completion(&goal, &key);
                let other = FunctionContractClaimKey::Ensure(1 - i);
                assert!(
                    goal.claims
                        .as_ref()
                        .unwrap()
                        .close(
                            &other,
                            ClaimGoalEvidence::Proposition(completion.clone()),
                            &goal.data.core.identity
                        )
                        .is_err()
                );
                goal.claims = Some(
                    goal.claims
                        .as_ref()
                        .unwrap()
                        .close(
                            &key,
                            ClaimGoalEvidence::Proposition(completion),
                            &goal.data.core.identity,
                        )
                        .unwrap(),
                );
            }
            finish(&mut progress, goal).unwrap();
            owner.accept_progress(&progress);
            assert_eq!(
                owner.first_open().is_none(),
                path == 1,
                "all live outcomes must contribute"
            );
        }
        assert!(owner.first_open().is_none());
        assert!(
            !owner.modular,
            "source-only proofs cannot create a reusable rule"
        );
        assert!(
            untouched.closed.is_empty(),
            "proof forks retain their own open cells"
        );
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
    fn ordinary_completion_installs_its_producer_directly() {
        let (entry, execution) =
            super::super::super::entry_authority_tests::checked_execution(0, None).unwrap();
        let whole = WholeContractProof::open(entry.clone()).unwrap();
        let root_owner = WholeContractRoot::open(entry).unwrap();
        let make_proof = || {
            let core = execution.open_outcome(0).unwrap();
            let mut closing = ContractClosingContext::new(&execution).open(0, &core);
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
            root(goal)
        };
        let proof = make_proof();
        let open = || {
            proof
                .open_contract_execution(
                    execution.clone(),
                    Some(&root_owner),
                    std::iter::once(proof.focused_branch()),
                )
                .unwrap()
        };
        assert!(open().finish().is_err(), "an opened outcome must complete");
        let (_, foreign) =
            super::super::super::entry_authority_tests::checked_execution(0, None).unwrap();
        assert!(
            proof
                .open_contract_execution(
                    foreign,
                    Some(&root_owner),
                    std::iter::once(proof.focused_branch())
                )
                .is_err(),
            "the producer is bound before any outcome proof runs"
        );
        let mut owner = open();
        let sibling = make_proof();
        assert!(
            sibling
                .complete_function_outcome_in_execution(&sibling, &mut owner)
                .is_err(),
            "another opening of the same producer has a different goal identity"
        );
        let completed = proof
            .complete_function_outcome_in_execution(&proof, &mut owner)
            .unwrap();
        assert!(
            proof
                .complete_function_outcome_in_execution(&proof, &mut owner)
                .is_err(),
            "completion is consumed exactly once"
        );
        let execution = completed
            .finish_contract_execution(owner)
            .unwrap()
            .into_execution();
        assert!(execution.closed_exit_obligations[0].is_some());
        assert!(
            whole
                .admit_executions(&[execution])
                .complete()
                .unwrap()
                .into_rule()
                .is_some()
        );
    }

    #[test]
    fn registration_consumes_ordinary_completion_without_scanning_receipts() {
        let (entry, execution) =
            super::super::super::entry_authority_tests::checked_execution(0, None).unwrap();
        let owner = WholeContractProof::open(entry).unwrap();
        let core = OutcomeProofCore {
            publication: None,
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
