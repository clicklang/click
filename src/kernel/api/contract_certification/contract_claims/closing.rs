//! Resource and write-footprint obligations owned by the outcome proof.

use super::*;
use crate::kernel::proof::{
    ContractClosingGoal, ContractClosingGoals, OutcomeClaimGoals, OutcomeIdentity,
    OutcomeProofCore, ProofFacts,
};
use std::sync::{Arc, OnceLock};

/// Shared declaration input of the closing goals, prepared once per proof.
pub(crate) struct ContractClosingContext {
    function: ProgramFunction,
    caller: ExecutionState,
    arguments: Vec<ProgramExpression>,
    entry_assumptions: PureFactContext,
    checked_entry: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    resource_claims: Vec<FunctionContractClaim>,
    resource_keys: Arc<BTreeSet<FunctionContractClaimKey>>,
    complete_boundary: bool,
    effect_claims: Vec<FunctionContractClaim>,
    entry: OnceLock<Result<ClosingEntry, String>>,
}

struct ClosingEntry {
    state: ExecutionState,
    resources: Option<Arc<[CheckedResourceFact]>>,
    projection: FunctionMemoryEffectProjection,
}

impl ContractClosingContext {
    #[cfg(test)]
    pub(crate) fn new(execution: &CheckedFunctionExecution) -> Arc<Self> {
        Self::for_resource_prefix(execution, execution.function.resource_ensures().len())
    }

    /// A clause-specific proof owes its jointly returned prefix, not clauses
    /// whose separate proofs have not run. The final prefix closes the boundary.
    pub(crate) fn for_resource_prefix(
        execution: &CheckedFunctionExecution,
        resource_prefix: usize,
    ) -> Arc<Self> {
        crate::instrumentation::record_deterministic_work(execution.arguments.len() + 1);
        let resource_claims = execution
            .function
            .contract_claims()
            .iter()
            .inspect(|_| {
                crate::instrumentation::record_deterministic_work(1);
            })
            .filter(|claim| {
                matches!(claim.target(), FunctionContractClaimTarget::EnsureResource(index) if *index < resource_prefix)
            })
            .cloned()
            .collect::<Vec<_>>();
        let resource_keys = Arc::new(
            resource_claims
                .iter()
                .map(|claim| claim.key().clone())
                .collect(),
        );
        Arc::new(Self {
            function: execution.function.clone(),
            caller: execution.allocation_entry_state().clone(),
            arguments: execution.function_arguments().to_vec(),
            entry_assumptions: execution.assumptions.clone(),
            checked_entry: execution.boundary_transfer.clone(),
            effect_claims: execution
                .function
                .contract_claims()
                .iter()
                .filter(|claim| matches!(claim.target(), FunctionContractClaimTarget::Effect))
                .cloned()
                .collect(),
            resource_claims,
            resource_keys,
            complete_boundary: resource_prefix >= execution.function.resource_ensures().len(),
            entry: OnceLock::new(),
        })
    }

    pub(crate) fn open(
        self: &Arc<Self>,
        path_index: usize,
        outcome: &OutcomeProofCore,
    ) -> ContractExitObligations {
        ContractExitObligations {
            context: self.clone(),
            path_index,
            outcome: outcome.identity.clone(),
            goals: ContractClosingGoals::open(),
            checked_transition: None,
            effects: None,
        }
    }

    fn entry(&self) -> Result<&ClosingEntry, ContractClosingRefusal> {
        self.entry
            .get_or_init(|| {
                let state = match &self.checked_entry {
                    Some(entry) => entry.callee_entry().clone(),
                    None => {
                        program_function_entry_state(&self.caller, &self.function, &self.arguments)
                            .ok_or_else(|| "could not bind the contract entry".to_string())?
                    }
                };
                let mut budget = ExecutionBudget::beside_live_state();
                let resources = if self.function.resource_derived_mutable_frame() {
                    let checked = if let Some(entry) = &self.checked_entry {
                        entry.checked_entry_clauses()
                    } else {
                        let (_, checked) = evaluate_function_resource_context_with_metadata(
                            &state,
                            self.function.resource_requires(),
                            self.function.composite_resource_definitions(),
                            &self.entry_assumptions.clone().assume_entry_clause_extents(),
                            &mut budget,
                        )
                        .map_err(|limit| limit.describe().to_string())?
                        .map_err(|error| error.kernel_summary())?;
                        checked
                    };
                    Some(checked.into())
                } else {
                    None
                };
                let projection = project_contract_memory_effects(
                    &state,
                    self.function.contract_interface(),
                    resources.as_deref(),
                    &self.entry_assumptions,
                    &mut budget,
                )
                .map_err(|limit| limit.describe().to_string())??;
                Ok(ClosingEntry {
                    state,
                    resources,
                    projection,
                })
            })
            .as_ref()
            .map_err(|reason| ContractClosingRefusal::Resource(reason.clone()))
    }
}

/// The contract closer opens these goals before post-execution tactics.
/// Checked resource transitions retain evidence; ordinary proof operations
/// discharge returned resources, allocation lifetime, and write footprints.
#[derive(Clone)]
pub(crate) struct ContractExitObligations {
    context: Arc<ContractClosingContext>,
    path_index: usize,
    outcome: OutcomeIdentity,
    goals: ContractClosingGoals,
    checked_transition: Option<CheckedResourceTransition>,
    effects: Option<Arc<PreparedEffectGoals>>,
}

/// Evidence supplied by the checked resource producer, not a closed goal.
#[derive(Clone, Copy)]
struct CheckedResourceTransition;

struct PreparedEffectGoals {
    base: ProofFacts,
    paths: Vec<CertifiedFunctionClaimPath>,
}

/// Evidence consumed by registration, never a request to check a path again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ClosedContractExit {
    path_index: usize,
    origin: Theorem,
    resources: Arc<BTreeSet<FunctionContractClaimKey>>,
    complete_boundary: bool,
}

impl ClosedContractExit {
    pub(crate) fn completes_boundary(&self) -> bool {
        self.complete_boundary
    }

    pub(in crate::kernel) fn path_index(&self) -> usize {
        self.path_index
    }
    pub(in crate::kernel) fn matches_path(&self, path: &SymbolicExecutionPath) -> bool {
        Arc::ptr_eq(&self.origin.proposition, &path.theorem.proposition)
    }
    pub(in crate::kernel) fn covers(&self, claim: &FunctionContractClaim) -> bool {
        match claim.target() {
            FunctionContractClaimTarget::EnsureResource(_) => self.resources.contains(claim.key()),
            FunctionContractClaimTarget::BodySafety => self.complete_boundary,
            FunctionContractClaimTarget::Effect => true,
            _ => false,
        }
    }

    #[cfg(test)]
    pub(super) fn fixture(path_index: usize, path: &SymbolicExecutionPath) -> Self {
        Self::fixture_for_claims(path_index, path, [])
    }

    #[cfg(test)]
    pub(super) fn fixture_for_claims(
        path_index: usize,
        path: &SymbolicExecutionPath,
        claims: impl IntoIterator<Item = FunctionContractClaimKey>,
    ) -> Self {
        Self {
            path_index,
            origin: path.theorem.clone(),
            resources: Arc::new(claims.into_iter().collect()),
            complete_boundary: true,
        }
    }
}

#[derive(Debug)]
pub(crate) enum ContractClosingRefusal {
    Resource(String),
    Claim(FunctionContractClaimKey),
    Runtime(RuntimeError),
    Write(Pointer),
    Range(MemoryRange),
    Storage(Vec<crate::kernel::functions::StorageWriteOutsideFootprint>),
    Pending(ContractClosingGoal),
}

impl ContractExitObligations {
    #[cfg(test)]
    pub(in crate::kernel) fn fixture_close_goal(&self, kind: ContractClosingGoal) -> Self {
        Self {
            goals: self.goals.close(kind),
            ..self.clone()
        }
    }

    pub(crate) fn first_open_goal(&self) -> Option<ContractClosingGoal> {
        self.goals.first_open()
    }

    pub(crate) fn after_resource_change(&self) -> Self {
        Self {
            goals: self
                .goals
                .reopen(ContractClosingGoal::ReturnedResources)
                .reopen(ContractClosingGoal::AllocationLifetime),
            checked_transition: None,
            effects: None,
            ..self.clone()
        }
    }

    /// Retain the checked producer's resource/lifetime evidence. Ordinary
    /// closing operations still discharge the corresponding goals, including
    /// any retained boundary refusal the resource producer does not cover.
    pub(crate) fn apply_resource_transition(
        &self,
        caller: &ExecutionState,
        outcome: FunctionOutcome,
        assumptions: &PureFactContext,
    ) -> Result<(Self, FunctionOutcome), String> {
        let outcome = checked_program_function_contract_resource_transition(
            caller,
            &self.context.function,
            &self.context.arguments,
            outcome,
            assumptions,
        )?;
        if let FunctionOutcome::RuntimeError(error) = &outcome {
            return Err(error.kernel_summary());
        }
        Ok((
            Self {
                checked_transition: Some(CheckedResourceTransition),
                ..self.clone()
            },
            outcome,
        ))
    }

    /// One primitive proof of the currently selected closing obligation.
    pub(crate) fn prove_goal(
        &self,
        kind: ContractClosingGoal,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        specification: &CheckedPathSpecification,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
    ) -> Result<Self, ContractClosingRefusal> {
        if !self.outcome.same_as(&outcome.identity) {
            return Err(ContractClosingRefusal::Resource(
                "closing obligations belong to another outcome".into(),
            ));
        }
        if self.first_open_goal() != Some(kind) {
            return Err(ContractClosingRefusal::Resource(
                "the selected closing goal is not open".into(),
            ));
        }
        let input_units = match kind {
            ContractClosingGoal::ReturnedResources => {
                self.context.resource_claims.len() + path.obligations().len() + 1
            }
            ContractClosingGoal::AllocationLifetime => self.context.resource_claims.len() + 1,
            ContractClosingGoal::WriteFootprint => {
                path.effect_facts.len() + self.context.effect_claims.len() + 1
            }
        };
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("contract closing", input_units);
        let mut proved = self.clone();
        match kind {
            ContractClosingGoal::ReturnedResources => {
                if !outcome.is_exceptional {
                    if let FunctionOutcome::RuntimeError(error) =
                        specification.specification().outcome()
                    {
                        if (self.context.complete_boundary && self.checked_transition.is_none())
                            || !crate::kernel::functions::is_deferred_conditional_resource_effect_error(error)
                        { return Err(ContractClosingRefusal::Runtime(error.clone())); }
                    }
                }
                let receipts_closed = !self.context.complete_boundary
                    || !execution
                        .deferred_contract_exits
                        .get(self.path_index)
                        .copied()
                        .unwrap_or(false);
                let resources_closed = self.checked_transition.is_some()
                    || receipts_closed
                        && matches!(
                            specification.specification().outcome(),
                            FunctionOutcome::Return { .. }
                        )
                        && self.resource_receipts_jointly_available(
                            outcome,
                            claims,
                            facts.assumptions(),
                        );
                let paths = self.prove_resource_goals(
                    execution,
                    path,
                    outcome,
                    claims,
                    facts,
                    !outcome.is_exceptional && !resources_closed,
                )?;
                if !self.context.effect_claims.is_empty() {
                    proved.effects = Some(Arc::new(PreparedEffectGoals {
                        base: facts.clone(),
                        paths,
                    }));
                }
            }
            ContractClosingGoal::AllocationLifetime => {
                if !outcome.is_exceptional
                    && self.context.complete_boundary
                    && self.checked_transition.is_none()
                {
                    self.prove_allocation_lifetime(outcome, claims, facts)?;
                }
            }
            ContractClosingGoal::WriteFootprint => {
                if !self.context.effect_claims.is_empty() {
                    let effects = self.effects.as_ref().ok_or_else(|| {
                        ContractClosingRefusal::Resource(
                            "the resource goal has not prepared the effect input".into(),
                        )
                    })?;
                    let delta = facts.introduced_since(&effects.base).ok_or_else(|| {
                        ContractClosingRefusal::Resource(
                            "the effect goal belongs to another proof context".into(),
                        )
                    })?;
                    let no_propositions = CheckedPropositionIndex::default();
                    for prepared in &effects.paths {
                        let assumptions =
                            assumptions_with_propositions(&prepared.assumptions, &delta);
                        for claim in &self.context.effect_claims {
                            if !function_claim_holds_on_prepared_path(
                                &self.context.function,
                                claim,
                                prepared,
                                &no_propositions,
                                None,
                                Some(&assumptions),
                            ) {
                                return Err(ContractClosingRefusal::Claim(claim.key().clone()));
                            }
                        }
                    }
                }
                self.prove_footprint(path, facts.assumptions())?;
            }
        }
        proved.goals = proved.goals.close(kind);
        Ok(proved)
    }

    /// Consume completed goal evidence; no semantic checker runs here.
    pub(crate) fn completion(
        &self,
        path: &SymbolicExecutionPath,
    ) -> Result<ClosedContractExit, ContractClosingRefusal> {
        if let Some(goal) = self.first_open_goal() {
            return Err(ContractClosingRefusal::Pending(goal));
        }
        Ok(ClosedContractExit {
            path_index: self.path_index,
            origin: path.theorem.clone(),
            resources: self.context.resource_keys.clone(),
            complete_boundary: self.context.complete_boundary,
        })
    }

    /// Clause receipts prove individual ownership. Consume their explicit
    /// returned units together: one surviving unit cannot return both a
    /// borrowed input and an additional produced unit.
    fn resource_receipts_jointly_available(
        &self,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        assumptions: &PureFactContext,
    ) -> bool {
        let mut remaining = outcome.state.resources().clone();
        for claim in &self.context.resource_claims {
            let Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) =
                claims.evidence(claim.key())
            else {
                return false;
            };
            if receipt.defers_resource_transition {
                return false;
            }
            for fact in receipt.returned_resources.facts() {
                let Some(next) = remaining.without_fact_incrementally(fact, assumptions) else {
                    return false;
                };
                remaining = next;
            }
        }
        true
    }

    fn prove_resource_goals(
        &self,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
        check_resources: bool,
    ) -> Result<Vec<CertifiedFunctionClaimPath>, ContractClosingRefusal> {
        let context = &self.context;
        // A successful checked transition has resolved this boundary. The
        // original execution's deferred marker predates post-return folds;
        // replaying it would discard the transition's established custody.
        let deferred = self.context.complete_boundary
            && self.checked_transition.is_none()
            && execution
                .deferred_contract_exits
                .get(self.path_index)
                .copied()
                .unwrap_or(false);
        if (!check_resources || context.resource_claims.is_empty())
            && context.effect_claims.is_empty()
            && !deferred
        {
            return Ok(Vec::new());
        }
        let cases = if deferred {
            contract_resource_condition_cases(
                &context.caller,
                &context.function,
                &context.arguments,
                &context.entry_assumptions,
            )
            .ok_or_else(|| {
                ContractClosingRefusal::Resource(
                    "could not create the conditional resource obligations".into(),
                )
            })?
        } else {
            vec![vec![]]
        };
        let checked_outcome = if outcome.is_exceptional {
            FunctionOutcome::Throw {
                value: outcome.result.as_ref().clone().into(),
                state: Box::new((*outcome.state).clone()),
            }
        } else {
            FunctionOutcome::Return {
                value: outcome.result.as_ref().clone().into(),
                state: Box::new((*outcome.state).clone()),
            }
        };
        let mut checked_claims = Vec::new();
        let mut returned = ResourceContext::new_with_equalities(facts.assumptions());
        for claim in &context.resource_claims {
            if let Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) =
                claims.evidence(claim.key())
            {
                checked_claims.push(claim.key().clone());
                if receipt.contributes_returned_resources {
                    returned = returned
                        .unchecked_with_facts(receipt.returned_resources.facts().iter().cloned());
                }
            }
        }
        let mut effect_paths = Vec::new();
        for case in cases {
            let mut path = path.clone();
            path.assumptions = assumptions_with_propositions(&path.assumptions, &case);
            let post = assumptions_with_propositions(facts.assumptions(), &case);
            if post.has_retained_contradiction() {
                continue;
            }
            path.post_assumptions = Some(post);
            let prepared = prepare_function_claim_path(
                &context.function,
                &path,
                checked_claims.clone(),
                false,
                deferred,
                execution
                    .deferred_contract_exit_errors
                    .get(self.path_index)
                    .cloned()
                    .flatten(),
                returned.clone(),
                false,
                execution.boundary_transfer.as_deref(),
                Some(&checked_outcome),
            )
            .map_err(|failure| ContractClosingRefusal::Resource(failure.reason))?;
            match &prepared.outcome {
                FunctionOutcome::RuntimeError(error) => {
                    return Err(ContractClosingRefusal::Runtime(error.clone()));
                }
                FunctionOutcome::UndefinedBehavior(error) => {
                    return Err(ContractClosingRefusal::Resource(format!(
                        "undefined behavior: {}",
                        error.description()
                    )));
                }
                _ => {}
            }
            let no_propositions = CheckedPropositionIndex::default();
            for claim in context.resource_claims.iter().filter(|_| check_resources) {
                if !function_claim_holds_on_prepared_path(
                    &context.function,
                    claim,
                    &prepared,
                    &no_propositions,
                    None,
                    None,
                ) {
                    return Err(ContractClosingRefusal::Claim(claim.key().clone()));
                }
            }
            if !context.effect_claims.is_empty() {
                effect_paths.push(prepared);
            }
        }
        Ok(effect_paths)
    }

    fn prove_allocation_lifetime(
        &self,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
    ) -> Result<(), ContractClosingRefusal> {
        let context = &self.context;
        let assumptions = facts.assumptions();
        let mut returned = ResourceContext::new_with_equalities(assumptions);
        let mut all_checked = !context.resource_claims.is_empty();
        let mut contributes = false;
        for claim in &context.resource_claims {
            match claims.evidence(claim.key()) {
                Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) => {
                    if receipt.defers_resource_transition {
                        return Ok(());
                    }
                    if receipt.contributes_returned_resources {
                        contributes = true;
                        returned = returned.unchecked_with_facts(
                            receipt.returned_resources.facts().iter().cloned(),
                        );
                    }
                }
                _ => all_checked = false,
            }
        }
        let mut budget = ExecutionBudget::beside_live_state();
        let result = if all_checked && contributes {
            crate::kernel::functions::unreturned_allocation_with_checked_returned_resources(
                &context.caller,
                &outcome.state,
                &outcome.result,
                &context.function,
                &context.arguments,
                &returned,
                assumptions,
                &mut budget,
            )
        } else {
            crate::kernel::functions::unreturned_allocation_at_function_exit(
                &context.caller,
                &outcome.state,
                &outcome.result,
                &context.function,
                &context.arguments,
                assumptions,
                &mut budget,
            )
            .map_err(|limit| ContractClosingRefusal::Resource(limit.describe()))?
        }
        .map_err(ContractClosingRefusal::Runtime)?;
        if let Some(obligation) = result {
            return Err(ContractClosingRefusal::Runtime(
                RuntimeError::LiveAllocationLeak {
                    allocation: Box::new(obligation.allocation().clone()),
                    resource: obligation.holder().cloned().map(Box::new),
                },
            ));
        }
        Ok(())
    }

    fn prove_footprint(
        &self,
        path: &SymbolicExecutionPath,
        assumptions: &PureFactContext,
    ) -> Result<(), ContractClosingRefusal> {
        let context = &self.context;
        let function = &context.function;
        let effects = &path.effect_facts;
        if function.contract_mutable().is_empty() && !function.resource_derived_mutable_frame() {
            check_empty_footprint(&context.caller, effects, assumptions)?;
        }
        if !function.contract_mutable().is_empty()
            || !function.resource_requires().is_empty()
            || function.resource_derived_mutable_frame()
        {
            let has_storage_write = crate::kernel::memory_effect_write_pointers(effects).iter().any(|pointer| pointer.block.is_static_storage_block())
                || effects.iter().any(|fact| matches!(fact.proposition(), Proposition::MemoryEffectSummary { mutable_ranges, .. } if mutable_ranges.iter().any(|range| range.base().block.is_static_storage_block())));
            if has_storage_write {
                let entry = context.entry()?;
                match storage_writes_outside_owned_footprint(
                    function,
                    &entry.state,
                    effects,
                    assumptions,
                    entry.resources.as_deref(),
                    Some(&entry.projection),
                )
                .map_err(|limit| ContractClosingRefusal::Resource(limit.describe().to_string()))?
                {
                    Some(outside) if outside.is_empty() => {}
                    Some(outside) => return Err(ContractClosingRefusal::Storage(outside)),
                    None => {
                        return Err(ContractClosingRefusal::Resource(
                            "could not evaluate the owned write footprint".into(),
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

/// The empty footprint is a resource/effect goal over the body's retained
/// effects. Proof-local facts cannot introduce additional program writes.
pub(crate) fn check_empty_footprint(
    caller: &ExecutionState,
    effects: &ExecutionFacts,
    assumptions: &PureFactContext,
) -> Result<(), ContractClosingRefusal> {
    for pointer in crate::kernel::memory_effect_write_pointers(effects) {
        if preexisting_write(&pointer, caller, assumptions) {
            return Err(ContractClosingRefusal::Write(pointer));
        }
    }
    for fact in effects {
        if let Proposition::MemoryEffectSummary {
            before,
            mutable_ranges,
            ..
        } = fact.proposition()
        {
            for range in mutable_ranges {
                if preexisting_write(range.base(), caller, assumptions)
                    && (!memory_holds_live_heap_allocation_at(before, range.base(), assumptions)
                        || memory_holds_live_heap_allocation_at(
                            caller.memory(),
                            range.base(),
                            assumptions,
                        ))
                {
                    return Err(ContractClosingRefusal::Range(range.clone()));
                }
            }
        }
    }
    Ok(())
}

fn preexisting_write(
    pointer: &Pointer,
    caller: &ExecutionState,
    assumptions: &PureFactContext,
) -> bool {
    if pointer.block.is_local_block() || pointer.block.is_havoc_block() {
        return false;
    }
    if !matches!(
        pointer.block,
        PointerBlock::Heap(_) | PointerBlock::Symbolic(_)
    ) {
        return true;
    }
    let memory = caller.memory();
    if !memory.has_nonlocal_storage() {
        return false;
    }
    if memory.is_live_heap_address(pointer, assumptions) {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut pending = vec![pointer.clone()];
    while let Some(candidate) = pending.pop() {
        if !seen.insert(candidate.clone()) {
            continue;
        }
        if !candidate.block.is_local_block()
            && !candidate.block.is_havoc_block()
            && (memory.has_block(&candidate.block)
                || memory.is_live_heap_address(&candidate, assumptions))
        {
            return true;
        }
        pending.extend(assumptions.exact_pointer_aliases(&candidate).cloned());
    }
    false
}
