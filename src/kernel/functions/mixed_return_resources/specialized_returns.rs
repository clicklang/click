//! Specialized return producers. Each consumes one selected returned occurrence;
//! consumers receive the emitted body rather than reconstructing its bindings.
use super::*;

pub(super) enum Construction {
    Body(Box<ConstructedReturnBody>),
    Unsupported,
}

#[derive(Clone, Copy)]
pub(super) enum Family {
    Instance,
    AuthorityControl,
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub(super) struct SpecializedReturnEvidence {
    pub(super) instance: Option<ResourceInstance>,
    pub(super) constructor: Option<AlgebraicTerm>,
    pub(super) authorities: Vec<(ResourceOccurrenceId, MachineTerm)>,
}

fn flat(specs: &[ResourceSpec]) -> bool {
    specs.iter().all(|spec| {
        crate::instrumentation::record_deterministic_work(1);
        !spec.is_view()
            && spec.quantity() == &ResourceQuantity::One
            && spec.guard().is_none()
            && spec.resource_arguments().is_empty()
            && matches!(
                spec.term(),
                ResourceTerm::Memory(_) | ResourceTerm::Token { .. }
            )
    })
}

pub(super) fn classify(
    support: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
) -> Option<Family> {
    if support.owned_quantity_term() != Some(&MachineTerm::constant(1)) {
        return None;
    }
    let name = match support.resource() {
        Resource::Instance(instance) => instance.name(),
        Resource::Composite { name, .. } => name,
        _ => return None,
    };
    let index = definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()?;
    let definition = &definitions[index];
    if definition.sealed
        || !definition.witnesses.is_empty()
        || !definition.children.is_empty()
        || !definition.resource_parameters.is_empty()
        || definition.recursive
    {
        return None;
    }
    match support.resource() {
        Resource::Instance(instance) => {
            if definition.instance_schema.as_ref() != Some(instance.schema())
                || !instance.resource_arguments().is_empty()
            {
                return None;
            }
            let supported = if let Some(matched) = &definition.matched {
                matched
                    .arms
                    .iter()
                    .all(|arm| arm.children.is_empty() && flat(&arm.contains))
            } else {
                flat(definition.contains())
            };
            supported.then_some(Family::Instance)
        }
        Resource::Composite { .. } => {
            if definition.matched.is_some()
                || definition.condition.is_some()
                || definition
                    .instance_schema
                    .as_ref()
                    .is_some_and(|schema| !schema.is_fieldless())
            {
                return None;
            }
            let mut authorities = 0;
            let supported = definition.contains().iter().all(|spec| {
                crate::instrumentation::record_deterministic_work(1);
                if spec.access() != ResourceAccessMode::Own
                    || spec.quantity() != &ResourceQuantity::One
                    || spec.guard().is_some()
                    || !spec.resource_arguments().is_empty()
                {
                    return false;
                }
                match spec.term() {
                    ResourceTerm::PopulationAuthority { .. } => {
                        authorities += 1;
                        true
                    }
                    ResourceTerm::Memory(_) => true,
                    ResourceTerm::Token { name, .. } => {
                        name == ResourceFact::ALLOCATION_RESOURCE_NAME
                    }
                    _ => false,
                }
            });
            (supported && (1..=2).contains(&authorities)).then_some(Family::AuthorityControl)
        }
        _ => None,
    }
}

fn opaque(
    support: &ResourceFact,
    source: ResourceOccurrenceId,
    evidence: SpecializedReturnEvidence,
) -> ConstructedReturnBody {
    ConstructedReturnBody {
        witnesses: BTreeMap::new(),
        specialized: Some(evidence),
        folded: vec![(support.clone(), source)],
        frontier: Vec::new(),
        viewed_children: Vec::new(),
        expansion: vec![support.clone()],
        boundary: Vec::new(),
        transfers: Vec::new(),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn construct(
    family: Family,
    support: &ResourceFact,
    source: ResourceOccurrenceId,
    clause: Option<usize>,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    composition: ReturnResourceComposition,
    borrowed: bool,
    assumptions: &PureFactContext,
) -> Option<Construction> {
    let name = match support.resource() {
        Resource::Instance(instance) => instance.name(),
        Resource::Composite { name, .. } => name,
        _ => return None,
    };
    let definition = &definitions[definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()?];
    let mut scratch = state.clone();
    scratch.locals = LocalEnvironment::default();
    scratch.resources = ResourceContext::new_with_equalities(assumptions);
    scratch.instance_field_scope = ResourceContext::new_with_equalities(assumptions);
    scratch.resource_bindings = None;
    let mut evidence = SpecializedReturnEvidence {
        instance: None,
        constructor: None,
        authorities: Vec::new(),
    };
    let mut evaluation = match (family, support.resource()) {
        (Family::Instance, Resource::Instance(instance)) => {
            evidence.instance = Some(instance.clone());
            instance_body_evaluation(&scratch, instance, definition).ok()?
        }
        (Family::AuthorityControl, Resource::Composite { arguments, .. }) => {
            if definition.parameters().len() != arguments.len() {
                return None;
            }
            for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                let value = argument.as_program_value()?;
                if value.program_type() != parameter.program_type() {
                    return None;
                }
                scratch.locals.bind_logical_typed(
                    parameter.name().to_owned(),
                    value.clone(),
                    parameter.program_type(),
                );
            }
            scratch
        }
        _ => return None,
    };
    let specs = if let Some(instance) = evidence.instance.as_ref() {
        if definition.matched.is_some() {
            let (arm, constructor) =
                match selected_instance_match_arm(instance, definition, definitions, assumptions) {
                    Ok(selection) => selection,
                    Err("resource match requires constructor evidence for the instance field") => {
                        return Some(Construction::Body(Box::new(opaque(
                            support, source, evidence,
                        ))));
                    }
                    Err(_) => return None,
                };
            let AlgebraicTermNode::Constructor { fields, .. } = &constructor.node else {
                return None;
            };
            for (name, value) in arm.bindings.iter().zip(fields) {
                if let AlgebraicValue::Program(value) = value {
                    evaluation.locals.bind_logical_typed(
                        name.clone(),
                        value.clone(),
                        value.program_type(),
                    );
                }
            }
            evidence.constructor = Some(constructor);
            &arm.contains
        } else {
            &definition.contains
        }
    } else {
        &definition.contains
    };
    let _checking = crate::instrumentation::CheckingWorkScope::new(
        "construct selected specialized return",
        definition.parameters().len()
            + specs.len()
            + evidence
                .instance
                .as_ref()
                .map_or(0, |instance| instance.fields().len())
            + 1,
    );
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .assume_entry_clause_spans()
        .assume_held_resource_domains();
    let mut budget = ExecutionBudget::beside_live_state();
    let active = match evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        &evaluation_assumptions,
        &mut budget,
    ) {
        Some(active) => active,
        None => {
            return Some(Construction::Body(Box::new(opaque(
                support, source, evidence,
            ))));
        }
    };
    let parameters = definition
        .parameters()
        .iter()
        .map(ProgramParameter::binding_name)
        .collect::<BTreeSet<_>>();
    let mut context = ResourceContext::new_with_equalities(assumptions);
    let mut transfers = Vec::new();
    let mut viewed_children = Vec::new();
    let mut authorities: Vec<ResourceFact> = Vec::new();
    let mut authority_sources = Vec::new();
    for (index, spec) in (if active { specs.as_slice() } else { &[] })
        .iter()
        .enumerate()
    {
        crate::instrumentation::record_deterministic_work(1);
        let authority = matches!(spec.term(), ResourceTerm::PopulationAuthority { .. });
        let fact = if authority {
            evaluate_population_authority_candidate(
                &evaluation,
                &evaluation,
                spec,
                &evaluation_assumptions,
                &mut budget,
            )
            .ok()?
            .ok()?
        } else {
            evaluate_function_resource_spec(&evaluation, spec, &evaluation_assumptions, &mut budget)
                .ok()?
                .ok()?
        };
        let origin = if fact.is_view() {
            ReturnOwnershipOrigin::Description
        } else if borrowed
            && (fixed_memory_shape(spec, &parameters).is_some()
                || definition.condition.is_none()
                    && summary_transfer::invariant_memory_shape(spec, &parameters))
        {
            ReturnOwnershipOrigin::EntryBorrow
        } else if definition.matched.is_none()
            && fact.memory_own_range().is_some()
            && let Some(clause) = clause
            && let Some(consumed) = composition.consumed_children()
            && let Some(transfer) = consumed.children.get(&vec![clause, index])
        {
            ReturnOwnershipOrigin::ConsumedCell(*transfer)
        } else if let Some((creator, events)) = composition.allocation_events() {
            FreshAllocationReturn::from_created_owner(&fact, creator, events)
                .map(ReturnOwnershipOrigin::FreshAllocation)
                .unwrap_or(ReturnOwnershipOrigin::Description)
        } else {
            ReturnOwnershipOrigin::Description
        };
        let (next, emitted) = match context.admit_without_discovery([fact.clone()], assumptions) {
            OwnershipAdmission::Admitted { context, inserted } => (context, inserted),
            OwnershipAdmission::Conflict(_) => {
                return None;
            }
            OwnershipAdmission::Unsupported(_) => {
                return Some(Construction::Unsupported);
            }
        };
        context = next;
        let child = emitted[0].1;
        if fact.is_view() {
            viewed_children.push((fact.clone(), child));
        }
        if authority {
            if let Some(first) = authorities.first() {
                let (Resource::PopulationAuthority(first), Resource::PopulationAuthority(current)) =
                    (first.resource(), fact.resource())
                else {
                    return None;
                };
                if first.arguments() != current.arguments() {
                    return None;
                }
            }
            authorities.push(fact.clone());
            authority_sources.push(child);
        }
        transfers.push(CompositeChildTransfer {
            source: child,
            parent: source,
            fact,
            origin,
        });
        evaluation.resources = context.clone();
    }
    // Only this new link to the live ledger needs establishing; no body is
    // lowered or validated again to obtain the count observations.
    evidence.authorities = authority_sources
        .into_iter()
        .zip(state.returned_authority_counts(&authorities).ok()?)
        .collect();
    let boundary = ResourceContext::new_with_equalities(assumptions)
        .unchecked_with_facts(
            transfers
                .iter()
                .filter(|transfer| transfer.origin == ReturnOwnershipOrigin::Description)
                .map(|transfer| transfer.fact.clone()),
        )
        .normalized_without_discovery(assumptions)
        .facts()
        .to_vec();
    let expansion = context
        .normalized_without_discovery(assumptions)
        .facts()
        .to_vec();
    Some(Construction::Body(Box::new(ConstructedReturnBody {
        witnesses: BTreeMap::new(),
        specialized: Some(evidence),
        folded: Vec::new(),
        frontier: expansion.clone(),
        expansion,
        boundary,
        transfers,
        viewed_children,
    })))
}
