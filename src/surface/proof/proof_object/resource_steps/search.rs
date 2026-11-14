//! Smart selection of a folded resource to open before retrying a statement.

use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// `solve`'s automatic opening (design/proof-reuse.md R4): the `unfold`
    /// of the one folded resource whose body holds `missing`, applied, so
    /// that `solve` can retry a C operation refused for want of it. `None`
    /// when no held resource's body holds it, or more than one does: `solve`
    /// never chooses which resource to open. A written `step()` never calls
    /// this.
    pub(in crate::surface::proof) fn try_open_for_missing_resource(
        search_input: &Proof<'a>,
        missing: &CResourceFact,
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
        let mut opening = None;
        for held in state.resources().composite_facts() {
            let CResourceFact::Own(CResource::Composite { name, arguments }, _) = held else {
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
            let Some(body) = definition.composite_body() else {
                continue;
            };
            let Some(clause) =
                held_composite_resource_clause(definition, arguments, parameter_binding, state)
            else {
                continue;
            };
            // The spelling is admitted only when it names the held resource.
            if !lower_resource_clause_at_state(&clause, parameter_binding, state)
                .is_ok_and(|lowered| lowered.resource() == held.resource())
            {
                continue;
            }
            let Ok(substitutions) = resource_argument_substitutions(
                definition,
                &clause,
                context.claim_label,
                context.tactic_index,
            ) else {
                continue;
            };
            let body_facts = body
                .contains()
                .iter()
                .filter_map(|contained| {
                    let contained = instantiate_resource_clause(contained, &substitutions).ok()?;
                    lower_resource_clause_at_state(&contained, parameter_binding, state).ok()
                })
                .collect::<Vec<_>>();
            if !crate::kernel::ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_facts(body_facts)
                .satisfies_fact(missing, assumptions)
            {
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
        crate::surface::proof::attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::UnfoldResource(clause)),
        )
    }
}

/// The source spelling `r(args)` of a held ordinary composite, its arguments
/// spelled from the frontier. `None` when an argument has no spelling.
fn held_composite_resource_clause(
    definition: &ResourceDefinition,
    arguments: &[AlgebraicValue],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Option<ResourceClause> {
    if arguments.len() != definition.parameters().len() {
        return None;
    }
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            AlgebraicValue::C(value) => {
                crate::surface::proof::surface_synthesis::synthesize_surface_value(
                    value,
                    parameter_binding,
                    state,
                )
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let parameter_types = definition
        .parameters()
        .iter()
        .map(|parameter| parameter.click_type().c_type())
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
