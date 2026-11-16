//! The ordinary root of a function-contract proof and its speculative scripts.

use super::*;
use crate::kernel::proof::PersistentVector;
use std::sync::Mutex;

#[derive(Clone)]
pub(crate) struct WholeContractRoot {
    plan: WholeContractProof,
    state: Arc<Mutex<Option<RootState>>>,
    program: Option<crate::kernel::termination::ProgramBodyOwner>,
}

struct RootState {
    goal: WholeContractProof,
    closed: PersistentMap<ContractCompletionGoal, ()>,
    executions: PersistentVector<Arc<CheckedFunctionExecution>>,
    subject: ProgramFunction,
    preferred_subject: bool,
    concrete_loop_exits: Option<Arc<crate::kernel::termination::loop_evidence::ConcreteLoopExits>>,
    loop_rules: PersistentVector<VerifiedLoopRule>,
    completed: Option<Arc<ContractBodyProof>>,
}

impl std::fmt::Debug for WholeContractRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WholeContractRoot")
            .field("plan", &self.plan)
            .finish_non_exhaustive()
    }
}

/// A script works on a persistent fork. Dropping a failed attempt publishes
/// neither its goal completions nor its execution metadata to its parent.
pub(crate) struct ContractRootAttempt {
    parent: WholeContractRoot,
    root: WholeContractRoot,
}

impl WholeContractRoot {
    pub(crate) fn open(entry: Arc<PreparedContractEntryCases>) -> Result<Self, String> {
        let plan = WholeContractProof::open(entry)?;
        Ok(Self::from_plan(plan.clone(), plan))
    }

    pub(in crate::kernel) fn open_in_program(
        entry: Arc<PreparedContractEntryCases>,
        program: &crate::kernel::ProgramContractBodies,
    ) -> Result<Self, String> {
        let mut root = Self::open(entry)?;
        root.program = Some(program.open_body(root.plan.entry.function.name().to_string()));
        Ok(root)
    }

    fn from_plan(plan: WholeContractProof, goal: WholeContractProof) -> Self {
        let subject = plan.entry.function.clone();
        Self {
            plan,
            program: None,
            state: Arc::new(Mutex::new(Some(RootState {
                goal,
                subject,
                closed: PersistentMap::default(),
                executions: PersistentVector::default(),
                preferred_subject: false,
                concrete_loop_exits: None,
                loop_rules: PersistentVector::default(),
                completed: None,
            }))),
        }
    }

    /// Open this owner's selected source loop before any of its proofs run.
    pub(crate) fn open_loop_proof(
        &self,
        index: usize,
        statement: ProgramStatement,
    ) -> Result<crate::kernel::StatementProofInput, TerminationError> {
        self.plan.entry.function.open_loop_proof(index, statement)
    }

    pub(in crate::kernel) fn plan(&self) -> &WholeContractProof {
        &self.plan
    }

    pub(crate) fn begin_attempt(&self) -> ContractRootAttempt {
        let state = self.state.lock().expect("contract root");
        let state = state
            .as_ref()
            .expect("a joined script is not a parent root");
        assert!(
            state.completed.is_none(),
            "the contract root has already completed"
        );
        ContractRootAttempt {
            parent: self.clone(),
            root: Self::from_plan(self.plan.clone(), state.goal.clone()),
        }
    }

    fn publish(
        &self,
        execution: Arc<CheckedFunctionExecution>,
        preferred: bool,
        loop_rules: Arc<[VerifiedLoopRule]>,
    ) {
        let mut state = self.state.lock().expect("contract root");
        let state = state.as_mut().expect("the strategy's script is still open");
        assert!(state.completed.is_none(), "the parent root is still open");
        let progress = execution
            .contract_completion
            .as_ref()
            .expect("a root-bound strategy retains its ordinary completion");
        // The affine execution operation captured this root at opening. These
        // are its own completed goals, not caller-supplied receipts to check.
        for goal in progress.closed.keys() {
            if state.goal.retire(goal.clone()) {
                state.closed.insert(goal.clone(), ());
            }
        }
        if state.executions.is_empty() || (preferred && !state.preferred_subject) {
            state.subject = execution.function.clone();
        }
        state.preferred_subject |= preferred;
        let exits = self
            .plan
            .loop_exits
            .completed(execution.execution_semantics.loops, loop_rules.iter());
        state.concrete_loop_exits = Some(match &state.concrete_loop_exits {
            Some(previous) => previous.intersect(&exits),
            None => exits,
        });
        state.executions.push(execution);
        for rule in loop_rules.iter() {
            crate::instrumentation::record_deterministic_work(1);
            state.loop_rules.push(rule.clone());
        }
    }

    /// Complete this ordinary body root. The only refusal is an already open
    /// declared goal; packaging the completed proof introduces no checks.
    pub(crate) fn finish(&self) -> Result<Arc<ContractBodyProof>, ContractCompletionGoal> {
        let mut state = self.state.lock().expect("contract root");
        let state = state
            .as_mut()
            .expect("a joined script is not a parent root");
        if let Some(completed) = &state.completed {
            return Ok(completed.clone());
        }
        if state.goal.proof.completion().is_none() {
            return Err(state
                .goal
                .first_open()
                .expect("an unfinished root has an open goal"));
        }
        // Visit the root's explicit execution outputs once to package the rule.
        // No artifact selection or reconstruction of obligation coverage occurs.
        let pointer_result = crate::kernel::object_types::published_execution_pointer_result(
            state.executions.iter().map(|execution| execution.as_ref()),
        );
        let loop_semantics = if state.executions.iter().all(|execution| {
            execution.execution_semantics.loops == LoopSemantics::ApplyVerifiedRules
        }) {
            LoopSemantics::ApplyVerifiedRules
        } else {
            LoopSemantics::Verify
        };
        let checked_callees = crate::kernel::termination::merge_checked_callees(
            state
                .executions
                .iter()
                .map(|execution| execution.checked_callees.as_ref()),
        )
        .unwrap_or_else(|| self.plan.declared_calls.clone());
        let mut applied_tactics = BTreeSet::new();
        for execution in state.executions.iter() {
            crate::instrumentation::record_deterministic_work(execution.applied_tactics.len() + 1);
            applied_tactics.extend(execution.applied_tactics.iter().cloned());
        }
        let exits = state
            .concrete_loop_exits
            .clone()
            .unwrap_or_else(|| self.plan.loop_exits.unknown());
        let termination =
            crate::kernel::termination::inputs::CompletedBodyTermination::from_completed_root(
                exits.clone(),
            );
        let rule = VerifiedFunctionRule {
            pointer_result,
            function: state.subject.clone(),
            descent_completion: self.plan.entry.function.contract_interface().has_call_ranked_recursion()
                .then(crate::kernel::termination::descent_completion::DescentCompletion::from_completed_root),
            concrete_loop_exits: Some(exits),
            loop_semantics,
            checked_callees: Some(checked_callees),
            applied_tactics,
        };
        let completed = Arc::new(ContractBodyProof {
            termination,
            rule,
            modular: self.plan.modular,
            loop_rules: state.loop_rules.iter().cloned().collect(),
        });
        if let Some(program) = &self.program {
            program.publish(completed.clone());
        }
        state.completed = Some(completed.clone());
        Ok(completed)
    }
}

impl ContractRootAttempt {
    pub(crate) fn root(&self) -> &WholeContractRoot {
        &self.root
    }

    /// Join a successfully checked script. A partial strategy never supplies
    /// path coverage for another strategy: only its fully closed cells arrive.
    pub(crate) fn commit(self) {
        let child = self
            .root
            .state
            .lock()
            .expect("contract script")
            .take()
            .expect("a script attempt is joined once");
        let mut parent = self.parent.state.lock().expect("contract root");
        let parent = parent.as_mut().expect("the parent proof is open");
        assert!(parent.completed.is_none(), "the parent root is still open");
        for goal in child.closed.keys() {
            if parent.goal.retire(goal.clone()) {
                parent.closed.insert(goal.clone(), ());
            }
        }
        for rule in child.loop_rules.iter() {
            crate::instrumentation::record_deterministic_work(1);
            parent.loop_rules.push(rule.clone());
        }
        if let Some(exits) = child.concrete_loop_exits {
            parent.concrete_loop_exits = Some(match &parent.concrete_loop_exits {
                Some(previous) => previous.intersect(&exits),
                None => exits,
            });
        }
        if !child.executions.is_empty() {
            if parent.executions.is_empty()
                || (child.preferred_subject && !parent.preferred_subject)
            {
                parent.subject = child.subject;
            }
            parent.preferred_subject |= child.preferred_subject;
            for execution in child.executions.iter() {
                parent.executions.push(execution.clone());
            }
        }
    }
}

/// Affine successor of the ordinary outcome proof. Surface may attach its
/// already-produced metadata, but cannot replace the execution or its root.
pub(crate) struct CompletedContractExecution {
    execution: Arc<CheckedFunctionExecution>,
    root: Option<WholeContractRoot>,
    loop_rules: Arc<[VerifiedLoopRule]>,
}

impl CompletedContractExecution {
    pub(super) fn new(
        execution: CheckedFunctionExecution,
        root: Option<WholeContractRoot>,
    ) -> Self {
        Self {
            execution: Arc::new(execution),
            root,
            loop_rules: Arc::from([]),
        }
    }
    pub(crate) fn with_loop_rules(mut self, rules: Arc<[VerifiedLoopRule]>) -> Self {
        self.loop_rules = rules;
        self
    }
    pub(crate) fn execution(&self) -> &Arc<CheckedFunctionExecution> {
        &self.execution
    }
    pub(crate) fn with_checked_resource_claims(
        mut self,
        claims: Vec<Vec<FunctionContractClaimKey>>,
    ) -> Self {
        self.execution =
            Arc::new(Arc::unwrap_or_clone(self.execution).with_checked_resource_claims(claims));
        self
    }
    pub(crate) fn with_checked_resource_transitions(mut self, transitions: Vec<bool>) -> Self {
        self.execution = Arc::new(
            Arc::unwrap_or_clone(self.execution).with_checked_resource_transitions(transitions),
        );
        self
    }
    pub(crate) fn with_checked_returned_resources(
        mut self,
        resources: Vec<ResourceContext>,
    ) -> Self {
        self.execution = Arc::new(
            Arc::unwrap_or_clone(self.execution).with_checked_returned_resources(resources),
        );
        self
    }
    pub(crate) fn publish(self, preferred: bool) {
        if let Some(root) = self.root {
            root.publish(self.execution, preferred, self.loop_rules);
        }
    }
    #[cfg(test)]
    pub(crate) fn into_execution(self) -> CheckedFunctionExecution {
        Arc::unwrap_or_clone(self.execution)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::*;

    fn fixture() -> (WholeContractRoot, CheckedFunctionExecution) {
        let (entry, execution) =
            crate::kernel::api::contract_certification::entry_authority_tests::checked_execution(
                0, None,
            )
            .unwrap();
        (WholeContractRoot::open(entry).unwrap(), execution)
    }

    fn prove_strategy(
        root: &WholeContractRoot,
        execution: CheckedFunctionExecution,
    ) -> CompletedContractExecution {
        let core = execution.open_outcome(0).unwrap();
        let mut closing = ContractClosingContext::new(&execution).open(0, &core);
        for goal in [
            ContractClosingGoal::ReturnedResources,
            ContractClosingGoal::AllocationLifetime,
            ContractClosingGoal::WriteFootprint,
        ] {
            closing = closing.fixture_close_goal(goal);
        }
        let mut goal =
            FunctionOutcomeObligation::new(0, Arc::new(OutcomeProofState::new(core, ())));
        goal.claims = Some(OutcomeClaimGoals::open([], false));
        goal.closing = Some(closing);
        let proof: ProofObject<
            (),
            crate::kernel::proof::ProofObligation<(), Arc<OutcomeProofState<()>>>,
            (),
        > = ProofObject::root(
            (),
            ProofBranch::new(
                crate::kernel::proof::ProofObligation::FunctionOutcome(goal),
                ProofBranchState {
                    facts: ProofFacts::default(),
                    unfolded_predicates: Default::default(),
                    execution: None,
                },
            ),
        );
        let mut owner = proof
            .open_contract_execution(
                execution,
                Some(root),
                std::iter::once(proof.focused_branch()),
            )
            .unwrap();
        proof
            .complete_function_outcome_in_execution(&proof, &mut owner)
            .unwrap()
            .finish_contract_execution(owner)
            .unwrap()
    }

    fn finish_program(
        program: crate::kernel::ProgramContractProof,
        rule: VerifiedFunctionRule,
    ) -> Result<
        Vec<crate::kernel::VerifiedFunctionTerminationRule>,
        crate::kernel::ProgramContractFailure,
    > {
        let rules = [rule];
        program
            .generate_termination(crate::kernel::ProgramTerminationInputs {
                independent: crate::kernel::IndependentTerminationInputs {
                    rules: &rules,
                    bodies: &[],
                },
                plans: &[],
                assumed_terminating: &BTreeSet::new(),
                diverging_contracts: &BTreeSet::new(),
                has_unselected_functions: false,
            })
            .and_then(|proof| proof.prove_implicitly())
            .map(|proof| proof.complete().into_termination_rules())
    }

    #[test]
    fn program_completion_waits_for_its_own_body_root() {
        let (entry, execution) =
            crate::kernel::api::contract_certification::entry_authority_tests::checked_execution(
                0, None,
            )
            .unwrap();
        let program = crate::kernel::ProgramContractProof::open(
            BTreeSet::from([entry.function.name().to_string()]),
            BTreeSet::new(),
            &BTreeSet::new(),
        );
        let _pending =
            WholeContractRoot::open_in_program(entry.clone(), &program.bodies()).unwrap();
        let unrelated = WholeContractRoot::open(entry).unwrap();
        prove_strategy(&unrelated, execution).publish(false);
        let unrelated_body = unrelated.finish().unwrap();
        assert!(
            matches!(
                finish_program(program, unrelated_body.into_rule().unwrap()),
                Err(crate::kernel::ProgramContractFailure::UnfinishedBody(_))
            ),
            "another root's completed body cannot close the captured parent goal"
        );
    }

    #[test]
    fn ordinary_body_completion_publishes_directly_to_the_captured_program() {
        let (entry, execution) =
            crate::kernel::api::contract_certification::entry_authority_tests::checked_execution(
                0, None,
            )
            .unwrap();
        let program = crate::kernel::ProgramContractProof::open(
            BTreeSet::from([entry.function.name().to_string()]),
            BTreeSet::new(),
            &BTreeSet::new(),
        );
        let root = WholeContractRoot::open_in_program(entry, &program.bodies()).unwrap();
        let attempt = root.begin_attempt();
        prove_strategy(attempt.root(), execution).publish(false);
        attempt.commit();
        let body = root.finish().unwrap();
        assert!(
            Arc::ptr_eq(&body, &root.finish().unwrap()),
            "cached completion does not publish twice"
        );
        assert_eq!(
            finish_program(program, body.into_rule().unwrap())
                .unwrap_or_else(|_| panic!("both body and termination closed"))
                .len(),
            1
        );
    }

    #[test]
    fn ordinary_root_completes_from_its_child_proof_without_artifact_admission() {
        let (root, execution) = fixture();
        assert!(root.finish().is_err());
        let attempt = root.begin_attempt();
        prove_strategy(attempt.root(), execution).publish(false);
        assert!(
            attempt
                .root
                .state
                .lock()
                .unwrap()
                .as_ref()
                .unwrap()
                .goal
                .proof
                .is_complete()
        );
        assert!(
            root.finish().is_err(),
            "a script has not joined its parent yet"
        );
        attempt.commit();
        let completed = root.finish().unwrap();
        assert!(completed.into_rule().is_some());
        assert!(
            Arc::ptr_eq(&completed, &root.finish().unwrap()),
            "reading a completed root performs no new checking"
        );
    }

    #[test]
    fn failed_and_sibling_scripts_preserve_the_parent_and_each_other() {
        let (root, execution) = fixture();
        let failed = root.begin_attempt();
        prove_strategy(failed.root(), execution.clone()).publish(false);
        drop(failed);
        assert!(
            root.finish().is_err(),
            "discarding a script cannot prove its parent"
        );
        assert!(
            root.state
                .lock()
                .unwrap()
                .as_ref()
                .unwrap()
                .executions
                .is_empty()
        );
        let selected = root.begin_attempt();
        let sibling = root.begin_attempt();
        prove_strategy(selected.root(), execution).publish(false);
        selected.commit();
        assert!(root.finish().is_ok());
        assert!(
            sibling
                .root
                .state
                .lock()
                .unwrap()
                .as_ref()
                .unwrap()
                .goal
                .first_open()
                .is_some()
        );
    }

    #[test]
    fn completed_execution_is_bound_to_the_root_that_opened_it() {
        let (root, execution) = fixture();
        let other = WholeContractRoot::open(root.plan.entry.clone()).unwrap();
        let attempt = root.begin_attempt();
        let completed = prove_strategy(attempt.root(), execution);
        assert!(other.finish().is_err());
        completed.publish(false);
        attempt.commit();
        assert!(root.finish().is_ok());
        assert!(
            other.finish().is_err(),
            "the receipt cannot publish into another root with the same entry"
        );
    }

    mod scaling_tests {
        include!(
            "../../../../../scaling_tests/kernel/api/contract_certification/contract_claims/root.rs"
        );
    }
}
