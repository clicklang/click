//! Clause-level resource rules retained by a contract, before application.
use super::*;

/// A consumed flat footprint can be returned once with the same spelling in
/// immutable call parameters. This recipe alone grants no ownership: application
/// must bind its input clause to the call's checked reservation.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct SummaryResourceTransferRule {
    pub(super) inputs_by_output: BTreeMap<usize, usize>,
    pub(super) inputs_by_child: BTreeMap<Vec<usize>, usize>,
}

impl SummaryResourceTransferRule {
    pub(in crate::kernel) fn compile(interface: &FunctionContractInterface) -> Self {
        let parameters = interface
            .parameters()
            .iter()
            .chain(interface.value_parameters())
            .map(|parameter| (parameter.binding_name(), parameter.program_type()))
            .collect::<BTreeMap<_, _>>();
        let identity = parameters
            .keys()
            .map(|name| {
                (
                    (*name).clone(),
                    ProgramExpression::Variable((*name).clone()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut inputs = BTreeMap::<_, VecDeque<usize>>::new();
        for (index, input) in interface.resource_requires().iter().enumerate() {
            if input.role() == ResourceTransferRole::Consume
                && let Some(key) = footprint(input, &parameters, &identity)
            {
                inputs.entry(key).or_default().push_back(index);
            }
        }
        let mut remaining = inputs.values().map(VecDeque::len).sum::<usize>();
        let mut rule = Self::default();
        for (index, output) in interface.resource_ensures().iter().enumerate() {
            if output.role() != ResourceTransferRole::Produce
                || output.state_source() != ResourceStateSource::Post
            {
                continue;
            }
            if let Some(key) = footprint(output, &parameters, &identity)
                && let Some(input) = inputs.get_mut(&key).and_then(VecDeque::pop_front)
            {
                rule.inputs_by_output.insert(index, input);
                remaining -= 1;
            }
        }
        // Analyze one selected finite definition, never an unfolded definition
        // tree. Nested/general bodies retain their existing transfer adapter.
        for (clause, output) in interface.resource_ensures().iter().enumerate() {
            if remaining == 0 {
                break;
            }
            if output.role() != ResourceTransferRole::Produce
                || output.state_source() != ResourceStateSource::Post
                || output.guard().is_some()
                || output.quantity() != &ResourceQuantity::One
            {
                continue;
            }
            let term = match output.term() {
                ResourceTerm::Instance { resource, .. } => resource.as_ref(),
                term => term,
            };
            let ResourceTerm::Composite {
                name, arguments, ..
            } = term
            else {
                continue;
            };
            let Some(definition) = interface.composite_resource_definition(name) else {
                continue;
            };
            if definition.is_recursive()
                || definition.matched.is_some()
                || !definition.children.is_empty()
                || !definition.witnesses.is_empty()
                || definition.contains().iter().any(|child| {
                    !matches!(
                        child.term(),
                        ResourceTerm::Memory(_) | ResourceTerm::Token { .. }
                    )
                })
            {
                continue;
            }
            let bindings = definition
                .parameters()
                .iter()
                .zip(arguments)
                .filter_map(|(formal, argument)| {
                    let value = resolve(argument, &identity)?;
                    let actual_type = match &value {
                        ProgramExpression::Variable(name) => *parameters.get(name)?,
                        ProgramExpression::Value(value) => value.program_type(),
                        _ => return None,
                    };
                    // A parameter conversion could move a bound (especially a
                    // narrowed lower bound) outside the reserved footprint.
                    (actual_type == formal.program_type())
                        .then(|| (formal.binding_name().clone(), value))
                })
                .collect::<BTreeMap<_, _>>();
            for (child, spec) in definition.contains().iter().enumerate() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(key) = footprint(spec, &parameters, &bindings)
                    && let Some(input) = inputs.get_mut(&key).and_then(VecDeque::pop_front)
                {
                    rule.inputs_by_child.insert(vec![clause, child], input);
                    remaining -= 1;
                }
            }
        }
        rule
    }
}

fn footprint(
    spec: &ResourceSpec,
    parameters: &BTreeMap<&BindingName, ProgramType>,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
) -> Option<(BindingName, ProgramExpression, ProgramExpression, u32)> {
    let ResourceTerm::Memory(segment) = spec.term() else {
        return None;
    };
    let ProgramExpression::Variable(base) = resolve(&segment.base, bindings)? else {
        return None;
    };
    if !parameters.get(&base)?.is_object_pointer()
        || spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || spec.guard().is_some()
        || segment.guard().is_some()
    {
        return None;
    }
    let start = resolve(&segment.start, bindings)?;
    let end = resolve(&segment.end, bindings)?;
    let bound = |expression: &ProgramExpression| match expression {
        ProgramExpression::Variable(name) => parameters.contains_key(name),
        _ => mixed_return_resources::fixed_memory_bound(expression).is_some(),
    };
    (bound(&start) && bound(&end)).then(|| (base, start, end, segment.element_width()))
}

fn resolve(
    expression: &ProgramExpression,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
) -> Option<ProgramExpression> {
    match expression {
        ProgramExpression::Variable(name) => bindings.get(name).cloned(),
        _ => mixed_return_resources::fixed_memory_bound(expression).map(ProgramExpression::Value),
    }
}

/// A borrowed body's memory clause reads only its retained arguments. No
/// post-memory load can change the footprint that entry already reserved.
pub(super) fn invariant_memory_shape(
    spec: &ResourceSpec,
    parameters: &BTreeSet<&BindingName>,
) -> bool {
    let ResourceTerm::Memory(segment) = spec.term() else {
        return false;
    };
    invariant_parameter_expression(&segment.base, parameters)
        && spec.access() == ResourceAccessMode::Own
        && spec.quantity() == &ResourceQuantity::One
        && spec.guard().is_none()
        && segment.guard().is_none()
        && invariant_parameter_expression(&segment.start, parameters)
        && invariant_parameter_expression(&segment.end, parameters)
}

// Retained arguments and fixed subobject addresses do not read post memory.
// Loads and local-address expressions deliberately stay opaque.
pub(super) fn invariant_parameter_expression(
    expression: &ProgramExpression,
    parameters: &BTreeSet<&BindingName>,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        ProgramExpression::Variable(name) => parameters.contains(name),
        ProgramExpression::Value(_) => true,
        ProgramExpression::Cast { expression, .. } => {
            invariant_parameter_expression(expression, parameters)
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            invariant_parameter_expression(pointer, parameters)
        }
        ProgramExpression::Add(left, right)
        | ProgramExpression::Subtract(left, right)
        | ProgramExpression::Multiply(left, right) => {
            invariant_parameter_expression(left, parameters)
                && invariant_parameter_expression(right, parameters)
        }
        _ => false,
    }
}

pub(super) fn invariant_body_condition(
    definition: &CompositeResourceDefinition,
    parameters: &BTreeSet<&BindingName>,
) -> bool {
    let Some(condition) = definition.condition.as_ref() else {
        return true;
    };
    let stable = |expression: &SpecExpression| match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::ProgramExpression(expression) => {
            invariant_parameter_expression(expression, parameters)
        }
        _ => false,
    };
    matches!(condition, SpecProposition::Comparison { left, right, .. } if stable(left) && stable(right))
}
