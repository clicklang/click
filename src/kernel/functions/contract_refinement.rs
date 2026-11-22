//! Whether a function's resource and memory-effect interface refines a named contract's: exact and framed resource transitions, access-mode adapters, and compatible mutable footprints.

use super::*;

#[derive(Debug)]
pub(crate) enum ContractRefinementPreparationError {
    Unsupported(String),
    Incompatible(&'static str),
    Evaluation {
        clause: &'static str,
        detail: Option<String>,
    },
    Stopped(ExecutionLimit),
}

impl From<ExecutionLimit> for ContractRefinementPreparationError {
    fn from(limit: ExecutionLimit) -> Self {
        Self::Stopped(limit)
    }
}

impl ContractRefinementPreparationError {
    pub(super) fn evaluating(clause: &'static str) -> Self {
        Self::Evaluation {
            clause,
            detail: None,
        }
    }

    fn evaluation_detail(clause: &'static str, detail: impl std::fmt::Display) -> Self {
        Self::Evaluation {
            clause,
            detail: Some(detail.to_string()),
        }
    }
}

/// Automatic compatibility only needs the verdict. Preserve evaluator stops
/// for callers that already distinguish them from ordinary incompatibility.
fn compatibility(result: Result<(), ContractRefinementPreparationError>) -> ExecutionResult<bool> {
    match result {
        Ok(()) => Ok(true),
        Err(ContractRefinementPreparationError::Stopped(limit)) => Err(limit),
        Err(_) => Ok(false),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn compatible_resource_and_effect_interfaces(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    contract_post: &ExecutionState,
    function_post: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    compatibility(check_refinement_interfaces(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_refinement_interfaces(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    contract_post: &ExecutionState,
    function_post: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), ContractRefinementPreparationError> {
    if !exact_resource_interfaces_match(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )? {
        framed_resource_transition_refines(
            contract,
            function,
            contract_entry,
            function_entry,
            contract_post,
            function_post,
            assumptions,
            budget,
        )?;
    }
    check_refinement_write_ranges(
        contract,
        function,
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

/// Check an access-mode variance at a refinement boundary with the same
/// checked transfer used by calls.  The algebraic framed-refinement check is
/// intentionally not sufficient here: it can establish that a view's value
/// is contained in an owned value without recording the borrow scope that makes
/// the implementation's observation valid.
///
/// `Some(true)` means an owned target requirement was adapted to a viewed
/// implementation requirement and its entry/recovery evidence was checked.
/// `Some(false)` is an explicit view-to-own refusal.  `None` means the two
/// interfaces have no access-mode variance that this adapter handles.
pub(super) fn checked_access_mode_refinement_adapter(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    function_post: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<bool>> {
    if contract.resource_requires().is_empty() || function.resource_requires().is_empty() {
        return Ok(None);
    }
    let Ok((contract_resources, _)) = evaluate_function_resource_context_with_metadata(
        contract_entry,
        contract.resource_requires(),
        contract.composite_resource_definitions(),
        &assumptions.clone().assume_entry_clause_spans(),
        budget,
    )?
    else {
        return Ok(Some(false));
    };
    let Ok((function_resources, _)) = evaluate_function_resource_context_with_metadata(
        function_entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        &assumptions.clone().assume_entry_clause_spans(),
        budget,
    )?
    else {
        return Ok(Some(false));
    };
    let satisfied_by_mode = |required: &ResourceFact, view: bool| {
        contract_resources.facts().iter().any(|available| {
            available.is_view() == view
                && ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(available.clone())
                    .satisfies_fact(required, assumptions)
        })
    };
    let mut own_to_view = false;
    for implementation in function_resources.facts() {
        if implementation.is_view() {
            // A same-mode view is already a shared capability.  Invoke the
            // borrow adapter only when this exact requirement is supplied by
            // ownership, including proper subranges; comparing resource
            // terms for equality would miss that common refinement.
            own_to_view |= !satisfied_by_mode(implementation, true)
                && satisfied_by_mode(implementation, false);
            continue;
        }
        let Some(view_requirement) = implementation.core_with_assumptions(assumptions) else {
            continue;
        };
        if !satisfied_by_mode(implementation, false) && satisfied_by_mode(&view_requirement, true) {
            // An implementation requiring exclusive authority cannot be
            // called through an interface that grants only observation.
            return Ok(Some(false));
        }
    }
    if !own_to_view {
        return Ok(None);
    }

    // Evaluate both sides into checked contexts before planning.  Supplying
    // these contexts is what makes the planner consume the exact target owner
    // rather than treating `satisfies_fact` as a capability conversion.
    let caller = contract_entry
        .clone()
        .with_resource_context(contract_resources);
    let callee = function_entry
        .clone()
        .with_resource_context(function_resources.clone());
    let mut transfer = match prepare_contract_resource_transfer(
        &caller,
        &callee,
        "refinement",
        function,
        assumptions,
        budget,
        false,
        ResourceTransitionPurpose::CallSite,
    )? {
        Ok(transfer) => transfer,
        Err(_) => return Ok(Some(false)),
    };
    let callee = callee_state_with_resource_transfer(callee, &transfer);
    let post = function_post
        .clone()
        .with_resource_context(function_resources);
    let ContractReturnResources {
        output_resources: _,
        escrow_boundary,
        return_resources: returned,
        ensured_views: returned_views,
        produced_borrowing_pieces,
        returned_entry_partition,
    } = match evaluate_contract_return_resources(
        &transfer.caller_resources_after_requirements,
        escrowed_owners(&transfer),
        &transfer.canonical_borrowed_owners,
        &transfer.borrowed_inputs,
        &transfer_entry_clauses(&transfer),
        &caller,
        &post,
        "refinement",
        function,
        &[],
        ReturnResourceComposition::ValidateDescriptions,
        assumptions,
        budget,
    )? {
        Ok(result) => result,
        Err(_) => return Ok(Some(false)),
    };
    transfer.returned_entry_partition = returned_entry_partition;
    transfer.candidate_output_views = returned_views;
    transfer.produced_borrowing_pieces = produced_borrowing_pieces;
    if recover_candidate_stable_view_resources(
        &caller,
        &callee,
        &transfer,
        returned,
        escrow_boundary,
        assumptions,
        assumptions,
        &[],
    )
    .is_err()
    {
        return Ok(Some(false));
    }
    Ok(Some(true))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn exact_resource_interfaces_match(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    contract_post: &ExecutionState,
    function_post: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.resource_requires().len() != function.resource_requires().len()
        || contract.resource_ensures().len() != function.resource_ensures().len()
    {
        return Ok(false);
    }
    for (contract_resource, function_resource) in contract
        .resource_requires()
        .iter()
        .zip(function.resource_requires())
    {
        let contract_resource = match evaluate_function_resource_spec_with_entry(
            contract_entry,
            contract_entry,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_resource = match evaluate_function_resource_spec_with_entry(
            function_entry,
            function_entry,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    for (contract_resource, function_resource) in contract
        .resource_ensures()
        .iter()
        .zip(function.resource_ensures())
    {
        let contract_state = match contract_resource.state_source() {
            ResourceStateSource::Entry => contract_entry,
            ResourceStateSource::Current | ResourceStateSource::Post => contract_post,
        };
        let contract_resource = match evaluate_function_resource_spec_with_entry(
            contract_entry,
            contract_state,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_state = match function_resource.state_source() {
            ResourceStateSource::Entry => function_entry,
            ResourceStateSource::Current | ResourceStateSource::Post => function_post,
        };
        let function_resource = match evaluate_function_resource_spec_with_entry(
            function_entry,
            function_state,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    Ok(true)
}

fn resource_fact_supports_framed_refinement(resource: &ResourceFact) -> bool {
    matches!(
        resource,
        ResourceFact::Own(Resource::Memory(_) | Resource::Instance(_), quantity)
            if quantity.as_const() == Some(1)
    ) || matches!(
        resource,
        ResourceFact::Own(Resource::Composite { .. } | Resource::Token { .. }, _)
            | ResourceFact::View(
                Resource::Memory(_) | Resource::Composite { .. } | Resource::Token { .. }
            )
    )
}

fn unsupported_framing_family(resource: &ResourceSpec) -> Option<ResourceFamily> {
    if resource.is_instance() {
        return match resource.instance_resource_spec() {
            Some(inner) => unsupported_framing_family(&inner),
            None => Some(ResourceFamily::Instance),
        };
    }
    let family = resource.family();
    (!matches!(
        family,
        ResourceFamily::Memory | ResourceFamily::Composite | ResourceFamily::Token
    ))
    .then_some(family)
}

/// Checks that the named requirements can supply the concrete requirements,
/// preserving everything the concrete transition only borrows or does not
/// need as a frame. Then requires the concrete ensures together with that
/// frame to provide the named ensures. The resource context's indexed
/// algebras perform ownership splitting, symbolic exact-resource quantity arithmetic, range containment,
/// exact token and folded-composite identity, and scoped borrowing; no project
/// functions, composite definitions, or unrelated proof state are inspected.
#[allow(clippy::too_many_arguments)]
fn framed_resource_transition_refines(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    contract_post: &ExecutionState,
    function_post: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), ContractRefinementPreparationError> {
    use ContractRefinementPreparationError::{Incompatible, Unsupported};
    if let Some(family) = contract
        .resource_requires()
        .iter()
        .chain(contract.resource_ensures())
        .chain(function.resource_requires())
        .chain(function.resource_ensures())
        .find_map(unsupported_framing_family)
    {
        return Err(Unsupported(format!(
            "Click cannot frame a resource of family `{}` in contract refinement",
            family.describe()
        )));
    }
    let evaluate = |state, specs, definitions, clause, budget: &mut ExecutionBudget| {
        evaluate_function_resource_context(state, specs, definitions, assumptions, budget)?
            .map_err(|error| ContractRefinementPreparationError::evaluation_detail(clause, error))
    };
    let contract_requires = evaluate(
        contract_entry,
        contract.resource_requires(),
        contract.composite_resource_definitions(),
        "the target contract's required resources",
        budget,
    )?;
    let function_requires = evaluate(
        function_entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        "the source contract's required resources",
        budget,
    )?;
    let function_ensures = evaluate(
        function_post,
        function.resource_ensures(),
        function.composite_resource_definitions(),
        "the source contract's returned resources",
        budget,
    )?;
    let contract_ensures = evaluate(
        contract_post,
        contract.resource_ensures(),
        contract.composite_resource_definitions(),
        "the target contract's returned resources",
        budget,
    )?;
    if let Some(resource) = [
        &contract_requires,
        &function_requires,
        &function_ensures,
        &contract_ensures,
    ]
    .into_iter()
    .flat_map(|resources| resources.facts())
    .find(|resource| !resource_fact_supports_framed_refinement(resource))
    {
        let detail = match resource {
            ResourceFact::Own(Resource::Memory(_) | Resource::Instance(_), quantity) => {
                let quantity = quantity.as_const().map_or_else(
                    || "a symbolic quantity".to_owned(),
                    |value| format!("quantity {value}"),
                );
                format!(
                    "the framed resource `{}` must have unit ownership, but has {quantity}",
                    resource.diagnostic_summary()
                )
            }
            _ => format!(
                "Click cannot frame `{}` in contract refinement",
                resource.diagnostic_summary()
            ),
        };
        return Err(Unsupported(detail));
    }

    let Some(frame) = contract_requires
        .clone()
        .without_facts(function_requires.facts(), assumptions)
    else {
        return Err(Incompatible(
            "the target contract does not supply the resources required by the source contract",
        ));
    };
    let concrete_output = match frame.try_compose_with_facts_delaying_normalization(
        function_ensures.facts().iter().cloned(),
        assumptions,
    ) {
        Ok(resources) => resources,
        Err(_) => {
            return Err(Incompatible(
                "the source contract's returned resources cannot be combined with the resources it leaves untouched",
            ));
        }
    };
    if !resource_context_definitionally_contains(
        &concrete_output,
        &contract_ensures,
        &[],
        contract_post.memory(),
        assumptions,
    ) {
        return Err(Incompatible(
            "the source contract does not return the resources promised by the target contract",
        ));
    }
    Ok(())
}

/// Checks that every range the implementation may write lies inside the
/// target's checked effect projection. Both projections are built from the
/// same transition/effect evaluator: resource-derived interfaces evaluate
/// their entry resource clauses into role-bearing facts, while explicit
/// interfaces evaluate their guarded segments. Surface `contract_mutable`
/// metadata is never walked as the semantic comparison itself.
///
/// Both guard questions are decided by [`refinement_route_proves`]: exact
/// membership in the refinement assumptions, or the frozen condition checker
/// on a bare condition. A guard this cannot settle is treated as unsettled,
/// which refuses the refinement rather than widening the checked footprint.
/// There is no proof site here to receive an obligation instead: this is a
/// boolean gate on a kernel-formed contract fact, so refusing is the
/// conservative equivalent of emitting one.
///
/// The walk over the contract's declared segments is not a selection. Its only
/// result is whether some declared segment covers the required range; no later
/// check consults which one, and a corpus probe (both fixture harnesses, plus
/// the since-deleted `c_named_contract_refinement_selects_guarded_segment`
/// mdtest) found exactly one
/// covering segment at every reached site. So this is a discharge, and a
/// finite disjunction over the declared segments would spell a choice that
/// nothing consumes.
pub(super) fn mutable_footprint_is_compatible_for_interfaces(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    compatibility(check_refinement_write_ranges(
        contract,
        function,
        contract_entry,
        function_entry,
        assumptions,
        budget,
    ))
}

fn check_refinement_write_ranges(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), ContractRefinementPreparationError> {
    if !contract.resource_derived_mutable_frame()
        && !function.resource_derived_mutable_frame()
        && (contract
            .contract_mutable()
            .iter()
            .any(|segment| segment.guard().is_some())
            || function
                .contract_mutable()
                .iter()
                .any(|segment| segment.guard().is_some()))
    {
        return check_guarded_refinement_write_ranges(
            contract,
            function,
            contract_entry,
            function_entry,
            assumptions,
            budget,
        );
    }
    let contract_projection =
        project_refinement_effects(contract, contract_entry, assumptions, budget)?.map_err(
            |reason| {
                ContractRefinementPreparationError::evaluation_detail(
                    "the target contract's permitted writes",
                    reason,
                )
            },
        )?;
    let function_projection =
        project_refinement_effects(function, function_entry, assumptions, budget)?.map_err(
            |reason| {
                ContractRefinementPreparationError::evaluation_detail(
                    "the source contract's permitted writes",
                    reason,
                )
            },
        )?;
    // Range containment is indexed by memory family and element width before
    // the proof-sensitive endpoint check. This avoids comparing every
    // implementation range with every unrelated target range while retaining
    // the shallow alias fallback for symbolic blocks.
    // An unnamed footprint may write any memory: a target that allows one
    // allows every implementation write, and an implementation that needs
    // one is allowed only by a target that allows one too.
    if contract_projection
        .ranges()
        .iter()
        .any(MemoryRange::is_unnamed_footprint)
    {
        return Ok(());
    }
    if function_projection
        .ranges()
        .iter()
        .any(MemoryRange::is_unnamed_footprint)
    {
        return Err(write_ranges_do_not_refine());
    }
    let mut available_by_family: BTreeMap<(AddressBase, u32), Vec<&MemoryRange>> = BTreeMap::new();
    for available in contract_projection.ranges() {
        available_by_family
            .entry((available.base.base.clone(), available.element_width))
            .or_default()
            .push(available);
    }
    if !function_projection.ranges().iter().all(|required_range| {
        if let Some(candidates) = available_by_family.get(&(
            required_range.base.base.clone(),
            required_range.element_width,
        )) {
            candidates.iter().any(|available_range| {
                memory_range_covers(available_range, required_range, assumptions)
            })
        } else {
            contract_projection.ranges().iter().any(|available_range| {
                memory_range_covers(available_range, required_range, assumptions)
            })
        }
    }) {
        return Err(write_ranges_do_not_refine());
    }
    Ok(())
}

fn write_ranges_do_not_refine() -> ContractRefinementPreparationError {
    ContractRefinementPreparationError::Incompatible(
        "the target contract does not cover all writes permitted by the source contract",
    )
}

/// Guarded explicit effects need one projection per implementation guard: the
/// implementation's guard is the active path assumption, while a target guard
/// must already be established on that path. Range lowering itself still goes
/// through the shared projection evaluator.
fn check_guarded_refinement_write_ranges(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), ContractRefinementPreparationError> {
    use ContractRefinementPreparationError as Refusal;
    let mut guard_assumptions = assumptions.clone();
    let Some(contract_guards) = lower_refinement_mutable_guards_for_interface(
        contract,
        contract_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Err(Refusal::evaluating(
            "a guard on the target contract's writes",
        ));
    };
    let Some(function_guards) = lower_refinement_mutable_guards_for_interface(
        function,
        function_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Err(Refusal::evaluating(
            "a guard on the source contract's writes",
        ));
    };
    for (required_segment, required_guard) in
        function.contract_mutable().iter().zip(function_guards)
    {
        if required_guard.as_ref().is_some_and(|guard| {
            refinement_route_proves(
                &guard_assumptions,
                &Proposition::Not(Box::new(guard.clone())),
            )
        }) {
            continue;
        }
        let mut active_assumptions = guard_assumptions.clone();
        if let Some(guard) = required_guard {
            active_assumptions = active_assumptions.assume_proposition(guard);
        }
        let required = project_explicit_memory_segments(
            function_entry,
            std::slice::from_ref(required_segment),
            &active_assumptions,
            budget,
            true,
        )?
        .map_err(|reason| {
            Refusal::evaluation_detail("a write range in the source contract", reason)
        })?;
        let Some(required_range) = required.ranges.first() else {
            return Err(Refusal::evaluating("a write range in the source contract"));
        };
        let mut covered = false;
        let mut evaluation_failure = None;
        for (available_segment, available_guard) in
            contract.contract_mutable().iter().zip(&contract_guards)
        {
            if let Some(guard) = available_guard
                && !refinement_route_proves(&active_assumptions, guard)
            {
                continue;
            }
            let mut available_segment = available_segment.clone();
            available_segment.guard = None;
            let available = match project_explicit_memory_segments(
                contract_entry,
                std::slice::from_ref(&available_segment),
                &active_assumptions,
                budget,
                true,
            )? {
                Ok(available) => available,
                Err(reason) => {
                    evaluation_failure.get_or_insert(reason);
                    continue;
                }
            };
            if available.ranges.iter().any(|available_range| {
                memory_range_covers(available_range, required_range, &active_assumptions)
            }) {
                covered = true;
                break;
            }
        }
        if !covered {
            return Err(match evaluation_failure {
                Some(reason) => {
                    Refusal::evaluation_detail("a write range in the target contract", reason)
                }
                None => write_ranges_do_not_refine(),
            });
        }
    }
    Ok(())
}

pub(super) fn project_refinement_effects(
    interface: &FunctionContractInterface,
    entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<FunctionMemoryEffectProjection, String>> {
    let mut projection_assumptions = assumptions.clone();
    // Explicit guards retain refinement's exact-route refusal semantics. The
    // resource-derived projection has no independent surface guard list and
    // therefore goes directly through the checked transition evaluator.
    if !interface.resource_derived_mutable_frame() {
        let Some(guards) = lower_refinement_mutable_guards_for_interface(
            interface,
            entry,
            &mut projection_assumptions,
            budget,
        )?
        else {
            return Ok(Err("mutable footprint guard is undecided".to_string()));
        };
        let mut ranges = Vec::new();
        let mut evidence_facts = Vec::new();
        for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
            let mut active_assumptions = projection_assumptions.clone();
            if let Some(guard) = guard {
                if refinement_route_proves(
                    &active_assumptions,
                    &Proposition::Not(Box::new(guard.clone())),
                ) {
                    continue;
                }
                active_assumptions = active_assumptions.assume_proposition(guard.clone());
                if !refinement_route_proves(&active_assumptions, &guard) {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
            }
            // Guard resolution above is the refinement-specific route. Feed
            // the now unconditional segment to the shared evaluator so range
            // lowering itself remains identical to call/certification paths.
            let mut segment = segment.clone();
            segment.guard = None;
            let Ok(projected) = project_explicit_memory_segments(
                entry,
                std::slice::from_ref(&segment),
                &active_assumptions,
                budget,
                true,
            )?
            else {
                return Ok(Err("could not evaluate mutable footprint".to_string()));
            };
            ranges.extend(projected.ranges);
            evidence_facts.extend(projected.evidence_facts);
        }
        return Ok(Ok(FunctionMemoryEffectProjection {
            ranges,
            evidence_facts: evidence_facts.into(),
            // Explicit segments carry no requirement source.
            range_sources: Vec::new(),
        }));
    }
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        None,
        &projection_assumptions,
        budget,
        true,
    )
}

#[cfg(test)]
pub(super) fn mutable_footprint_is_compatible(
    contract: &ProgramFunction,
    function: &ProgramFunction,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    mutable_footprint_is_compatible_for_interfaces(
        contract.contract_interface(),
        function.contract_interface(),
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

pub(super) fn lower_refinement_mutable_guards_for_interface(
    interface: &FunctionContractInterface,
    entry: &ExecutionState,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<Option<Proposition>>>> {
    let mut guards = Vec::with_capacity(interface.contract_mutable().len());
    for segment in interface.contract_mutable() {
        let Some(guard) = segment.guard() else {
            guards.push(None);
            continue;
        };
        if !spec_proposition_is_state_independent(guard) {
            return Ok(None);
        }
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            entry,
            guard,
            Some(entry),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(None);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) {
            return Ok(None);
        }
        guards.push(Some(path.proposition.clone()));
    }
    Ok(Some(guards))
}
