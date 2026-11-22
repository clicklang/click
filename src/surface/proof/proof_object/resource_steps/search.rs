//! Smart selection of a folded resource to open before retrying a statement.

use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Spell the exact head already selected by call preparation. Only
    /// ordinary, fact-free bodies can use this certificate rewrite: an
    /// explicit open must introduce no new proof names or body facts.
    pub(in crate::surface::proof) fn selected_call_supplier_unfold(
        input: &Proof<'a>,
        selected: &ResourceFact,
    ) -> Option<ProofStep> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_call_supplier_unfold");
        let ProofContext::Execution(context) = input.context.as_ref() else {
            return None;
        };
        let Resource::Composite { name, arguments } = selected.resource() else {
            return None;
        };
        let state = input.execution()?.core.reached_state();
        if selected.owned_quantity() != Some(1) || state.resources().exact_count(selected) != 1 {
            return None;
        }
        let definition = context.resource_environment.get(name)?;
        let body = definition.composite_body()?;
        if definition.is_authorized()
            || definition.is_sealed()
            || !definition.is_fieldless()
            || !definition.resource_parameters().is_empty()
            || body.condition().is_some()
            || !body.facts().is_empty()
            || !body.witnesses().is_empty()
            || body.matched.is_some()
            || !body.children.is_empty()
        {
            return None;
        }
        let parameters = context.parameter_binding();
        let clause = held_composite_resource_clause(
            definition,
            &arguments.native_values(),
            parameters,
            context.constants.function_entry_state.as_ref(),
            state,
        )?;
        let lowered = lower_resource_clause_at_state(&clause, parameters, state).ok()?;
        (lowered == *selected).then_some(ProofStep::UnfoldResource(clause))
    }

    /// `solve`'s automatic opening (design/proof-reuse.md R4): the `unfold`
    /// of the one folded resource whose body holds `missing`, applied, so
    /// that `solve` can retry a C operation refused for want of it. `None`
    /// when no held resource's body holds it, or more than one does: `solve`
    /// never chooses which resource to open. A written `step()` never calls
    /// this.
    pub(in crate::surface::proof) fn try_open_for_missing_resource(
        search_input: &Proof<'a>,
        missing: &ResourceFact,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_open_for_missing_resource");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = search_input.execution() else {
            return Ok(None);
        };
        let state = &execution.core.state;
        let parameter_binding = context.parameter_binding();
        let assumptions = search_input.facts().assumptions();
        // A held instance's arguments may be values only the function's
        // entry holds, spelled `old(...)`: they lower at the entry state.
        let entry = context
            .constants
            .function_entry_state
            .as_ref()
            .unwrap_or(state);
        let lower = |clause: &ResourceClause| {
            crate::surface::lowering::lower_resource_clause_at_current_locals_with_entry_and_assumptions(
                clause,
                parameter_binding,
                entry,
                state,
                None,
                assumptions,
            )
        };
        let mut opening = None;
        for held in state.resources().composite_facts() {
            let ResourceFact::Own(Resource::Composite { name, arguments }, _) = held else {
                continue;
            };
            let Some(definition) = context.resource_environment.get(name) else {
                continue;
            };
            // Population members exchange through their authority, which
            // this one-layer opening does not reach.
            if definition.is_authorized() {
                continue;
            }
            if definition.composite_body().is_none() {
                continue;
            }
            let Some(clause) = held_composite_resource_clause(
                definition,
                &(arguments).native_values(),
                parameter_binding,
                context.constants.function_entry_state.as_ref(),
                state,
            ) else {
                continue;
            };
            // The spelling is admitted only when it names the held resource.
            if !lower(&clause).is_ok_and(|lowered| lowered.resource() == held.resource()) {
                continue;
            }
            // The body holds `missing`, or holds a resource whose own body
            // does: a box inside an option of one, opened one layer per
            // retry.
            let body_facts = |definition: &ResourceDefinition,
                              clause: &ResourceClause|
             -> Option<Vec<ResourceFact>> {
                let body = definition.composite_body()?;
                let substitutions = resource_argument_substitutions(
                    definition,
                    clause,
                    context.claim_label,
                    context.tactic_index,
                )
                .ok()?;
                Some(
                    body.contains()
                        .iter()
                        .filter_map(|contained| {
                            let contained =
                                instantiate_resource_clause(contained, &substitutions).ok()?;
                            lower(&contained).ok()
                        })
                        .collect(),
                )
            };
            let holds = |facts: &[ResourceFact]| {
                crate::kernel::ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_facts(facts.to_vec())
                    .satisfies_fact(missing, assumptions)
            };
            let Some(outer) = body_facts(definition, &clause) else {
                continue;
            };
            // A resource the body holds whose pointer argument is the
            // missing memory's base: the box inside an option of one. This
            // only proposes the outer opening; the retried operation decides.
            // The missing memory's base, or the allocation token's pointer.
            let missing_base = missing
                .memory_range()
                .map(|range| range.base().base.clone())
                .or_else(|| missing.allocation().map(|(base, _)| base.base.clone()));
            let inner_holds = || {
                outer.iter().any(|inner| {
                    let ResourceFact::Own(Resource::Composite { arguments, .. }, _) = inner else {
                        return false;
                    };
                    arguments.native_values().iter().any(|argument| {
                        matches!(argument, AlgebraicValue::Program(ProgramValue::Pointer(pointer))
                            if Some(&pointer.address().base) == missing_base.as_ref())
                    })
                })
            };
            // The held resource's own pointer argument is the missing
            // memory's base: a box whose contents are read.
            let direct = (*arguments).native_values().iter().any(|argument| {
                matches!(argument, AlgebraicValue::Program(ProgramValue::Pointer(pointer))
                    if Some(&pointer.address().base) == missing_base.as_ref())
            });
            if !holds(&outer) && !direct && !inner_holds() {
                continue;
            }
            if opening.is_some() {
                return Ok(None);
            }
            opening = Some(clause);
        }
        let Some(clause) = opening else {
            return Ok(None);
        };
        let applied = search_input
            .driver()
            .apply_step(ProofStep::UnfoldResource(clause));
        crate::surface::proof::attempt::candidate_outcome(applied)
    }
}

/// The source spelling `r(args)` of a held ordinary composite, its arguments
/// spelled from the frontier. `None` when an argument has no spelling.
fn held_composite_resource_clause(
    definition: &ResourceDefinition,
    arguments: &[AlgebraicValue],
    parameter_binding: ParameterBinding<'_>,
    entry: Option<&ExecutionState>,
    state: &ExecutionState,
) -> Option<ResourceClause> {
    if arguments.len() != definition.parameters().len() {
        return None;
    }
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            AlgebraicValue::Program(value) => {
                crate::surface::proof::surface_synthesis::synthesize_surface_value_at_entry_and_post(
                    value,
                    parameter_binding,
                    entry,
                    state,
                )
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let parameter_types = definition
        .parameters()
        .iter()
        .map(|parameter| parameter.click_type().interface_type())
        .collect::<Option<Vec<_>>>()?;
    Some(ResourceClause::Declared {
        access: ResourceAccessMode::Own,
        kind: ResourceKind::Composite,
        name: definition.name().to_string(),
        arguments,
        type_schema: definition.field_schema().cloned(),
        resource_type_arguments: Vec::new(),
        resource_arguments: Vec::new(),
        parameter_types,
    })
}
