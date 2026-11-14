//! Resource and write-footprint obligations owned by the outcome proof.

use super::*;
use crate::kernel::proof::{OutcomeClaimGoals, OutcomeIdentity, OutcomeProofCore, ProofFacts};
use std::sync::{Arc, OnceLock};

/// Shared declaration input of the closing goals, prepared once per proof.
pub(crate) struct CContractClosingContext {
    function: CFunction,
    caller: CState,
    arguments: Vec<CExpression>,
    entry_assumptions: PureFactContext,
    checked_entry: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    resource_claims: Vec<CFunctionContractClaim>,
    resource_keys: Arc<BTreeSet<CFunctionContractClaimKey>>,
    effect_claims: Vec<CFunctionContractClaim>,
    entry: OnceLock<Result<ClosingEntry, String>>,
}

struct ClosingEntry {
    state: CState,
    resources: Option<Arc<[CCheckedResourceFact]>>,
    projection: CFunctionMemoryEffectProjection,
}

impl CContractClosingContext {
    pub(crate) fn new(execution: &CCheckedFunctionExecution) -> Arc<Self> {
        crate::instrumentation::record_deterministic_work(execution.arguments.len() + 1);
        let resource_claims = execution
            .function
            .contract_claims()
            .iter()
            .inspect(|_| {
                crate::instrumentation::record_deterministic_work(1);
            })
            .filter(|claim| {
                matches!(
                    claim.target(),
                    CFunctionContractClaimTarget::EnsureResource(_)
                )
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
            arguments: execution.arguments.clone(),
            entry_assumptions: execution.assumptions.clone(),
            checked_entry: execution.boundary_transfer.clone(),
            effect_claims: execution
                .function
                .contract_claims()
                .iter()
                .filter(|claim| matches!(claim.target(), CFunctionContractClaimTarget::Effect))
                .cloned()
                .collect(),
            resource_claims,
            resource_keys,
            entry: OnceLock::new(),
        })
    }

    pub(crate) fn open(
        self: &Arc<Self>,
        path_index: usize,
        outcome: &OutcomeProofCore,
    ) -> CContractExitObligations {
        CContractExitObligations {
            context: self.clone(),
            path_index,
            outcome: outcome.identity.clone(),
            resources_closed: false,
            footprint_closed: false,
        }
    }

    fn entry(&self) -> Result<&ClosingEntry, CContractClosingRefusal> {
        self.entry
            .get_or_init(|| {
                let state = match &self.checked_entry {
                    Some(entry) => entry.callee_entry().clone(),
                    None => c_function_entry_state(&self.caller, &self.function, &self.arguments)
                        .ok_or_else(|| "could not bind the contract entry".to_string())?,
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
            .map_err(|reason| CContractClosingRefusal::Resource(reason.clone()))
    }
}

/// The contract closer opens both goals before any post-execution tactics.
/// Returned resource transitions do not discharge allocation lifetime or
/// joint boundary obligations; those retain their own closing goal.
#[derive(Clone)]
pub(crate) struct CContractExitObligations {
    context: Arc<CContractClosingContext>,
    path_index: usize,
    outcome: OutcomeIdentity,
    resources_closed: bool,
    footprint_closed: bool,
}

/// Evidence consumed by registration, never a request to check a path again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CClosedContractExit {
    path_index: usize,
    origin: Theorem,
    resources: Arc<BTreeSet<CFunctionContractClaimKey>>,
}

impl CClosedContractExit {
    pub(in crate::kernel) fn path_index(&self) -> usize {
        self.path_index
    }
    pub(in crate::kernel) fn matches_path(&self, path: &SymbolicCExecutionPath) -> bool {
        Arc::ptr_eq(&self.origin.proposition, &path.theorem.proposition)
    }
    pub(in crate::kernel) fn covers(&self, claim: &CFunctionContractClaim) -> bool {
        match claim.target() {
            CFunctionContractClaimTarget::EnsureResource(_) => self.resources.contains(claim.key()),
            CFunctionContractClaimTarget::Effect | CFunctionContractClaimTarget::BodySafety => true,
            _ => false,
        }
    }

    #[cfg(test)]
    pub(super) fn fixture(path_index: usize, path: &SymbolicCExecutionPath) -> Self {
        Self::fixture_for_claims(path_index, path, [])
    }

    #[cfg(test)]
    pub(super) fn fixture_for_claims(
        path_index: usize,
        path: &SymbolicCExecutionPath,
        claims: impl IntoIterator<Item = CFunctionContractClaimKey>,
    ) -> Self {
        Self {
            path_index,
            origin: path.theorem.clone(),
            resources: Arc::new(claims.into_iter().collect()),
        }
    }
}

#[derive(Debug)]
pub(crate) enum CContractClosingRefusal {
    Resource(String),
    Claim(CFunctionContractClaimKey),
    Runtime(CRuntimeError),
    Write(Pointer),
    Range(CMemoryRange),
    Storage(Vec<crate::kernel::functions::StorageWriteOutsideFootprint>),
}

impl CContractExitObligations {
    pub(crate) fn after_resource_change(&self) -> Self {
        Self {
            resources_closed: false,
            ..self.clone()
        }
    }

    /// Apply the returned resource transition. Lifetime and boundary goals
    /// remain open: this operation does not prove either of them.
    pub(crate) fn apply_resource_transition(
        &self,
        caller: &CState,
        outcome: CFunctionOutcome,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CFunctionOutcome), String> {
        let outcome = checked_c_function_contract_resource_transition(
            caller,
            &self.context.function,
            &self.context.arguments,
            outcome,
            assumptions,
        )?;
        if let CFunctionOutcome::RuntimeError(error) = &outcome {
            return Err(error.kernel_summary());
        }
        Ok((self.clone(), outcome))
    }

    /// Discharge the remaining ordinary closing goals, using the checked
    /// outcome and the claim completions retained on this exact proof branch.
    pub(crate) fn close(
        &self,
        execution: &CCheckedFunctionExecution,
        path: &SymbolicCExecutionPath,
        specification: &CheckedPathSpecification,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
    ) -> Result<(Self, CClosedContractExit), CContractClosingRefusal> {
        if !self.outcome.same_as(&outcome.identity) {
            return Err(CContractClosingRefusal::Resource(
                "closing obligations belong to another outcome".into(),
            ));
        }
        let mut closed = self.clone();
        if !outcome.is_exceptional {
            if !closed.resources_closed {
                if let CFunctionOutcome::RuntimeError(error) =
                    specification.specification().outcome()
                {
                    return Err(CContractClosingRefusal::Runtime(error.clone()));
                }
                closed.prove_resource_goals(execution, path, claims, facts)?;
                closed.prove_allocation_lifetime(outcome, claims, facts)?;
                closed.resources_closed = true;
            }
            if !closed.footprint_closed {
                closed.prove_footprint(path, facts.assumptions())?;
                closed.footprint_closed = true;
            }
        } else {
            closed.resources_closed = true;
            closed.footprint_closed = true;
        }
        Ok((
            closed,
            CClosedContractExit {
                path_index: self.path_index,
                origin: path.theorem.clone(),
                resources: self.context.resource_keys.clone(),
            },
        ))
    }

    fn prove_resource_goals(
        &self,
        execution: &CCheckedFunctionExecution,
        path: &SymbolicCExecutionPath,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
    ) -> Result<(), CContractClosingRefusal> {
        let context = &self.context;
        if context.resource_claims.is_empty() && context.effect_claims.is_empty() {
            return Ok(());
        }
        let deferred = execution
            .deferred_contract_exits
            .get(self.path_index)
            .copied()
            .unwrap_or(false);
        let cases = if deferred {
            contract_resource_condition_cases(
                &context.caller,
                &context.function,
                &context.arguments,
                &context.entry_assumptions,
            )
            .ok_or_else(|| {
                CContractClosingRefusal::Resource(
                    "could not create the conditional resource obligations".into(),
                )
            })?
        } else {
            vec![vec![]]
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
            )
            .map_err(|failure| CContractClosingRefusal::Resource(failure.reason))?;
            let no_propositions = CheckedPropositionIndex::default();
            for claim in context.resource_claims.iter().chain(&context.effect_claims) {
                if !function_claim_holds_on_prepared_path(
                    &context.function,
                    claim,
                    &prepared,
                    &no_propositions,
                    None,
                ) {
                    return Err(CContractClosingRefusal::Claim(claim.key().clone()));
                }
            }
        }
        Ok(())
    }

    fn prove_allocation_lifetime(
        &self,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &ProofFacts,
    ) -> Result<(), CContractClosingRefusal> {
        let context = &self.context;
        let assumptions = facts.assumptions();
        let mut returned = ResourceContext::new_with_equalities(assumptions);
        let mut all_checked = !context.resource_claims.is_empty();
        let mut contributes = false;
        for claim in &context.resource_claims {
            match claims.evidence(claim.key()) {
                Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) => {
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
            .map_err(|limit| CContractClosingRefusal::Resource(limit.describe()))?
        }
        .map_err(CContractClosingRefusal::Runtime)?;
        if let Some(obligation) = result {
            return Err(CContractClosingRefusal::Runtime(
                CRuntimeError::LiveAllocationLeak {
                    allocation: Box::new(obligation.allocation().clone()),
                    resource: obligation.holder().cloned().map(Box::new),
                },
            ));
        }
        Ok(())
    }

    fn prove_footprint(
        &self,
        path: &SymbolicCExecutionPath,
        assumptions: &PureFactContext,
    ) -> Result<(), CContractClosingRefusal> {
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
                || effects.iter().any(|fact| matches!(fact.proposition(), Proposition::CMemoryEffectSummary { mutable_ranges, .. } if mutable_ranges.iter().any(|range| range.base().block.is_static_storage_block())));
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
                .map_err(|limit| CContractClosingRefusal::Resource(limit.describe().to_string()))?
                {
                    Some(outside) if outside.is_empty() => {}
                    Some(outside) => return Err(CContractClosingRefusal::Storage(outside)),
                    None => {
                        return Err(CContractClosingRefusal::Resource(
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
    caller: &CState,
    effects: &ExecutionFacts,
    assumptions: &PureFactContext,
) -> Result<(), CContractClosingRefusal> {
    for pointer in crate::kernel::memory_effect_write_pointers(effects) {
        if preexisting_write(&pointer, caller, assumptions) {
            return Err(CContractClosingRefusal::Write(pointer));
        }
    }
    for fact in effects {
        if let Proposition::CMemoryEffectSummary {
            before,
            mutable_ranges,
            ..
        } = fact.proposition()
        {
            for range in mutable_ranges {
                if preexisting_write(range.base(), caller, assumptions)
                    && (!c_memory_holds_live_heap_allocation_at(before, range.base(), assumptions)
                        || c_memory_holds_live_heap_allocation_at(
                            caller.memory(),
                            range.base(),
                            assumptions,
                        ))
                {
                    return Err(CContractClosingRefusal::Range(range.clone()));
                }
            }
        }
    }
    Ok(())
}

fn preexisting_write(pointer: &Pointer, caller: &CState, assumptions: &PureFactContext) -> bool {
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
