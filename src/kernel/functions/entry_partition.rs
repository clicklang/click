//! Construct the partition asserted by a raw contract-entry section.

use super::*;

/// Elaborate the explicit raw section before publishing its entry hypothesis.
/// A declaration supplies descriptions, not held-body expansion evidence:
/// every written memory occurrence reaches admission, including duplicates.
/// The admitted entry retains its original folded storage and occurrence IDs.
pub(crate) fn admit_declared_entry_resources(
    descriptions: ResourceContext,
    state: &ExecutionState,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<ResourceContext, RuntimeError> {
    if descriptions.storage.index.instances.is_empty()
        && descriptions.owned_composite_facts().is_empty()
    {
        // Flat clauses already use the section producer's indexed admission.
        return Ok(descriptions);
    }
    // No unrelated caller frame participates in raw body evaluation.
    let state = state.clone().with_resource_context(descriptions.clone());
    let body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .assume_entry_clause_spans()
        .assume_held_resource_domains();
    enum Work {
        Clause(ResourceFact),
        EndBody(String),
    }
    let mut pending = descriptions
        .facts()
        .iter()
        .rev()
        .cloned()
        .map(Work::Clause)
        .collect::<Vec<_>>();
    let mut active = BTreeSet::new();
    let mut memory = Vec::new();
    while let Some(work) = pending.pop() {
        let fact = match work {
            Work::EndBody(name) => {
                active.remove(&name);
                continue;
            }
            Work::Clause(fact) => fact,
        };
        crate::instrumentation::record_deterministic_work(1);
        if !fact.is_own() || !fact.has_proven_positive_quantity(assumptions) {
            continue;
        }
        let name = match fact.resource() {
            Resource::Memory(_) => {
                memory.push(fact);
                continue;
            }
            Resource::Instance(instance) => instance.name(),
            Resource::Composite { name, .. } => name,
            _ => continue,
        };
        if active.contains(name) {
            // Retain a recursive tail as its own asserted resource. A raw
            // declaration never supplies an infinitely unfolded frontier.
            continue;
        }
        let index = definitions
            .binary_search_by(|definition| definition.name().cmp(name))
            .map_err(|_| {
                RuntimeError::FunctionContract("entry resource has no declared body".into())
            })?;
        let definition = &definitions[index];
        let mut evaluation = match fact.resource() {
            Resource::Instance(instance) => instance_body_evaluation(&state, instance, definition)
                .map_err(|message| RuntimeError::FunctionContract(message.into()))?,
            Resource::Composite { arguments, .. } => {
                if definition.instance_schema.is_some() || !definition.witnesses.is_empty() {
                    // A witness or field-bearing body has no native frontier
                    // until its own opening supplies those values.
                    continue;
                }
                let mut evaluation = ExecutionState::at_point(&state.program_point())
                    .with_resource_context(descriptions.clone());
                if arguments.len() != definition.parameters().len() {
                    return Err(RuntimeError::TypeMismatch);
                }
                for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                    let value = argument
                        .as_program_value()
                        .ok_or(RuntimeError::TypeMismatch)?;
                    evaluation.locals.set_typed(
                        parameter.binding_name().clone(),
                        value.clone(),
                        parameter.program_type(),
                    );
                }
                evaluation
            }
            _ => unreachable!(),
        };
        let contains: &[ResourceSpec] = if let Resource::Instance(instance) = fact.resource()
            && definition.matched.is_some()
        {
            let Ok((arm, constructor)) =
                selected_instance_match_arm(instance, definition, definitions, assumptions)
            else {
                // Keep an undecided arm conditional; never union exclusive arms.
                continue;
            };
            let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
                unreachable!("selected_instance_match_arm returns a constructor");
            };
            if fields
                .iter()
                .any(|field| field.as_program_value().is_none())
            {
                continue;
            }
            for (name, value) in arm.bindings.iter().zip(&fields) {
                let value = value.as_program_value().expect("native fields above");
                let ty = value.program_type();
                evaluation.locals.set_typed(name.clone(), value.clone(), ty);
            }
            &arm.contains
        } else {
            definition.contains()
        };
        let mut budget = ExecutionBudget::beside_live_state();
        if evaluate_composite_resource_body_condition(
            definition,
            &evaluation,
            &body_assumptions,
            &mut budget,
        ) != Some(true)
        {
            continue;
        }
        let clauses = contains
            .iter()
            .filter(|clause| {
                matches!(
                    clause.term(),
                    ResourceTerm::Memory(_) | ResourceTerm::Composite { .. }
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        // Evaluate raw clauses without first constructing/normalizing a held
        // body. The one frontier admission below establishes their partition.
        let children = evaluate_resource_clauses_against_whole_section(
            &evaluation,
            &evaluation,
            &clauses,
            &[],
            &body_assumptions,
            &mut budget,
        )
        .map_err(|limit| {
            RuntimeError::FunctionContract(format!(
                "declared entry body stopped at {}",
                limit.describe(),
            ))
        })??;
        active.insert(name.to_owned());
        pending.push(Work::EndBody(name.to_owned()));
        pending.extend(
            children
                .into_iter()
                .rev()
                .map(|child| Work::Clause(child.fact)),
        );
    }
    ResourceContext::new_with_equalities(assumptions)
        .install_established_partition(memory, assumptions)
        .map_err(resource_context_runtime_error)?;
    Ok(descriptions)
}
