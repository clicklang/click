//! Clause-level resource rules retained by a contract, before application.
use super::*;

/// A consumed flat footprint can be returned once with the same spelling in
/// immutable call parameters. This recipe alone grants no ownership: application
/// must bind its input clause to the call's checked reservation.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct SummaryResourceTransferRule {
    pub(super) inputs_by_output: BTreeMap<usize, usize>,
}

impl SummaryResourceTransferRule {
    pub(in crate::kernel) fn compile(interface: &FunctionContractInterface) -> Self {
        let parameters = interface
            .parameters()
            .iter()
            .chain(interface.value_parameters())
            .map(|parameter| (parameter.binding_name(), parameter.program_type()))
            .collect::<BTreeMap<_, _>>();
        let mut inputs = BTreeMap::<_, VecDeque<usize>>::new();
        for (index, input) in interface.resource_requires().iter().enumerate() {
            if input.role() == ResourceTransferRole::Consume
                && let Some(key) = footprint(input, &parameters)
            {
                inputs.entry(key).or_default().push_back(index);
            }
        }
        let mut rule = Self::default();
        for (index, output) in interface.resource_ensures().iter().enumerate() {
            if output.role() != ResourceTransferRole::Produce
                || output.state_source() != ResourceStateSource::Post
            {
                continue;
            }
            if let Some(key) = footprint(output, &parameters)
                && let Some(input) = inputs.get_mut(&key).and_then(VecDeque::pop_front)
            {
                rule.inputs_by_output.insert(index, input);
            }
        }
        rule
    }
}

fn footprint(
    spec: &ResourceSpec,
    parameters: &BTreeMap<&BindingName, ProgramType>,
) -> Option<(BindingName, ProgramExpression, ProgramExpression, u32)> {
    let ResourceTerm::Memory(segment) = spec.term() else {
        return None;
    };
    let ProgramExpression::Variable(base) = &segment.base else {
        return None;
    };
    if !parameters.get(base)?.is_object_pointer()
        || spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || spec.guard().is_some()
        || segment.guard().is_some()
    {
        return None;
    }
    let bound = |expression: &ProgramExpression| match expression {
        ProgramExpression::Variable(name) => parameters.contains_key(name),
        _ => mixed_return_resources::fixed_memory_bound(expression).is_some(),
    };
    (bound(&segment.start) && bound(&segment.end)).then(|| {
        (
            base.clone(),
            segment.start.clone(),
            segment.end.clone(),
            segment.element_width(),
        )
    })
}
