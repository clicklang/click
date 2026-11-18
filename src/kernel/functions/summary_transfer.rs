//! Clause-level resource rules retained by a contract, before application.
use super::*;

/// A consumed flat footprint can be returned once with the same spelling in
/// immutable call parameters. This recipe alone grants no ownership: application
/// must bind its input clause to the call's checked reservation.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct SummaryResourceTransferRule {
    pub(super) inputs_by_output: BTreeMap<usize, usize>,
    pub(super) inputs_by_child: BTreeMap<Vec<usize>, usize>,
    pub(super) projected_inputs: BTreeMap<Vec<usize>, usize>,
    pub(super) borrowed_instance_outputs: BTreeSet<usize>,
}

impl SummaryResourceTransferRule {
    pub(in crate::kernel) fn compile(interface: &FunctionContractInterface) -> Self {
        let parameters = interface
            .parameters()
            .iter()
            .chain(interface.value_parameters())
            .map(|parameter| (parameter.binding_name(), parameter.program_type()))
            .collect::<BTreeMap<_, _>>();
        let identity = parameter_bindings(parameters.keys().copied());
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
        // Model fields are post-state, while the borrowed head's immutable
        // arguments and exclusive binder retain their entry identity.
        let borrowed_instances = interface
            .resource_requires()
            .iter()
            .filter_map(|input| {
                if input.role() != ResourceTransferRole::Borrow
                    || input.is_view()
                    || input.guard().is_some()
                    || input.quantity() != &ResourceQuantity::One
                    || !input.resource_arguments().is_empty()
                {
                    return None;
                }
                let ResourceTerm::Instance { resource, .. } = input.term() else {
                    return None;
                };
                let ResourceTerm::Composite {
                    arguments,
                    argument_state_sources,
                    ..
                } = resource.as_ref()
                else {
                    return None;
                };
                if arguments.len() != argument_state_sources.len() {
                    return None;
                }
                arguments
                    .iter()
                    .zip(argument_state_sources)
                    .all(|(argument, source)| {
                        *source == ResourceStateSource::Entry
                            || immutable_expression(argument, &identity, &BTreeMap::new()).is_some()
                    })
                    .then_some(input.term())
            })
            .collect::<BTreeSet<_>>();
        for (index, output) in interface.resource_ensures().iter().enumerate() {
            if output.role() == ResourceTransferRole::Borrow
                && !output.is_view()
                && output.guard().is_none()
                && output.quantity() == &ResourceQuantity::One
                && output.resource_arguments().is_empty()
                && borrowed_instances.contains(output.term())
            {
                rule.borrowed_instance_outputs.insert(index);
            }
        }
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
        let used = rule
            .inputs_by_output
            .values()
            .chain(rule.inputs_by_child.values())
            .copied()
            .collect::<BTreeSet<_>>();
        let aliases = post_parameter_aliases(interface, &identity);
        let mut leaves = BTreeMap::<_, VecDeque<usize>>::new();
        let mut fragments = ConstantInputFragments::default();
        for (input, spec) in interface.resource_requires().iter().enumerate() {
            if spec.role() != ResourceTransferRole::Consume || used.contains(&input) {
                continue;
            }
            for (_, key) in immutable_leaves(
                spec,
                input,
                interface,
                &identity,
                &parameters,
                &BTreeMap::new(),
            ) {
                if let Some((base, start, end)) = constant_memory_span(&key) {
                    fragments.insert(base, start, end, input);
                } else {
                    leaves.entry(key).or_default().push_back(input);
                }
            }
        }
        for (output, spec) in interface.resource_ensures().iter().enumerate() {
            if spec.role() != ResourceTransferRole::Produce
                || spec.state_source() != ResourceStateSource::Post
            {
                continue;
            }
            for (path, key) in
                immutable_leaves(spec, output, interface, &identity, &parameters, &aliases)
            {
                if path.len() == 1 && rule.inputs_by_output.contains_key(&output)
                    || rule.inputs_by_child.contains_key(&path)
                {
                    continue;
                }
                let input = if let Some((base, start, end)) = constant_memory_span(&key) {
                    fragments.take(&base, start, end)
                } else {
                    leaves.get_mut(&key).and_then(VecDeque::pop_front)
                };
                if let Some(input) = input {
                    rule.projected_inputs.insert(path, input);
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
    let bindings = parameter_bindings(parameters.iter().copied());
    immutable_memory_key(spec, &bindings, &BTreeMap::new())
        .is_some_and(|(base, _, _, _)| parameter_address(&base))
}

fn parameter_address(expression: &ProgramExpression) -> bool {
    match expression {
        ProgramExpression::Variable(_) => true,
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => parameter_address(pointer),
        ProgramExpression::Cast { expression, .. } => parameter_address(expression),
        ProgramExpression::AddressOf(lvalue) | ProgramExpression::CheckedObjectAddress(lvalue) => {
            match lvalue.as_ref() {
                ProgramExpression::Load(pointer)
                | ProgramExpression::TypedLoad { pointer, .. }
                | ProgramExpression::Index(pointer, _) => parameter_address(pointer),
                _ => false,
            }
        }
        _ => false,
    }
}

fn parameter_bindings<'a>(
    names: impl Iterator<Item = &'a BindingName>,
) -> BTreeMap<BindingName, ProgramExpression> {
    let names = names.collect::<Vec<_>>();
    let mut bindings = names
        .iter()
        .map(|name| {
            (
                (*name).clone(),
                ProgramExpression::Variable((*name).clone()),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut aliases = BTreeMap::<String, Vec<&BindingName>>::new();
    for name in names {
        if let Some(spelling) = name.source_spelling() {
            aliases.entry(spelling.to_owned()).or_default().push(name);
        }
    }
    for (spelling, names) in aliases {
        let alias = BindingName::Named(spelling);
        if names.len() == 1 && !bindings.contains_key(&alias) {
            bindings.insert(alias, ProgramExpression::Variable(names[0].clone()));
        }
    }
    bindings
}

type ImmutableMemoryKey = (ProgramExpression, ProgramExpression, ProgramExpression, u32);

fn immutable_expression(
    expression: &ProgramExpression,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
    aliases: &BTreeMap<ProgramExpression, ProgramExpression>,
) -> Option<ProgramExpression> {
    if let Some(alias) = aliases.get(expression) {
        return Some(alias.clone());
    }
    let mut resolved = expression.clone();
    match &mut resolved {
        ProgramExpression::Variable(name) => return bindings.get(name).cloned(),
        ProgramExpression::Value(_) => {}
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            **pointer = immutable_expression(pointer, bindings, aliases)?;
        }
        ProgramExpression::Cast {
            expression,
            target_type,
            ..
        } if target_type.is_object_pointer() => {
            **expression = immutable_expression(expression, bindings, aliases)?;
        }
        ProgramExpression::AddressOf(lvalue) | ProgramExpression::CheckedObjectAddress(lvalue) => {
            match lvalue.as_mut() {
                ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
                    **pointer = immutable_expression(pointer, bindings, aliases)?;
                }
                ProgramExpression::Index(pointer, index) => {
                    **pointer = immutable_expression(pointer, bindings, aliases)?;
                    **index = immutable_expression(index, bindings, aliases)?;
                }
                _ => return None,
            }
        }
        _ => return None,
    }
    Some(resolved)
}

fn immutable_memory_key(
    spec: &ResourceSpec,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
    aliases: &BTreeMap<ProgramExpression, ProgramExpression>,
) -> Option<ImmutableMemoryKey> {
    let ResourceTerm::Memory(segment) = spec.term() else {
        return None;
    };
    if spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || spec.guard().is_some()
        || segment.guard().is_some()
    {
        return None;
    }
    Some((
        immutable_expression(&segment.base, bindings, aliases)?,
        immutable_expression(&segment.start, bindings, aliases)?,
        immutable_expression(&segment.end, bindings, aliases)?,
        segment.element_width(),
    ))
}

/// Compile fixed byte partitions from explicit clauses. Each allocation
/// withdraws its bytes, so a consumed whole object may supply disjoint fields
/// but cannot supply an overlapping sibling a second time.
type ConstantMemoryBase = (ProgramExpression, ProgramType);
#[derive(Default)]
struct ConstantInputFragments(BTreeMap<ConstantMemoryBase, BTreeMap<i128, (i128, usize)>>);
impl ConstantInputFragments {
    fn insert(&mut self, base: ConstantMemoryBase, start: i128, end: i128, input: usize) {
        self.0
            .entry(base)
            .or_default()
            .entry(start)
            .or_insert((end, input));
    }
    fn take(&mut self, base: &ConstantMemoryBase, start: i128, end: i128) -> Option<usize> {
        let slots = self.0.get_mut(base)?;
        let (&lo, &(hi, input)) = slots.range(..=start).next_back()?;
        if hi < end {
            return None;
        }
        slots.remove(&lo);
        if lo < start {
            slots.insert(lo, (start, input));
        }
        if end < hi {
            slots.insert(end, (hi, input));
        }
        Some(input)
    }
}

fn constant_memory_span(key: &ImmutableMemoryKey) -> Option<(ConstantMemoryBase, i128, i128)> {
    fn integer(expression: &ProgramExpression) -> Option<i128> {
        match expression {
            ProgramExpression::Value(ProgramValue::Int32(value)) => {
                value.as_const().map(|value| i128::from(value as i32))
            }
            ProgramExpression::Value(ProgramValue::Int64(value)) => {
                value.int64_as_const().map(i128::from)
            }
            ProgramExpression::Value(ProgramValue::UInt64(value)) => {
                value.uint64_as_const().map(i128::from)
            }
            _ => None,
        }
    }
    fn address(expression: &ProgramExpression) -> Option<(ProgramExpression, i128)> {
        match expression {
            ProgramExpression::Variable(_) | ProgramExpression::Value(ProgramValue::Pointer(_)) => {
                Some((expression.clone(), 0))
            }
            ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
                let (base, offset) = address(pointer)?;
                Some((base, offset.checked_add(i128::from(*bytes))?))
            }
            ProgramExpression::Subobject { pointer, .. } => address(pointer),
            ProgramExpression::Cast {
                expression,
                target_type,
                ..
            } if target_type.is_object_pointer() => address(expression),
            ProgramExpression::AddressOf(lvalue)
            | ProgramExpression::CheckedObjectAddress(lvalue) => match lvalue.as_ref() {
                ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
                    address(pointer)
                }
                _ => None,
            },
            _ => None,
        }
    }
    let (base, offset) = address(&key.0)?;
    let (ProgramExpression::Value(start_value), ProgramExpression::Value(end_value)) =
        (&key.1, &key.2)
    else {
        return None;
    };
    let kind = start_value.program_type();
    if end_value.program_type() != kind {
        return None;
    }
    let width = i128::from(key.3);
    let start = offset.checked_add(integer(&key.1)?.checked_mul(width)?)?;
    let end = offset.checked_add(integer(&key.2)?.checked_mul(width)?)?;
    (start < end).then_some(((base, kind), start, end))
}

fn immutable_leaves(
    spec: &ResourceSpec,
    clause: usize,
    interface: &FunctionContractInterface,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
    types: &BTreeMap<&BindingName, ProgramType>,
    aliases: &BTreeMap<ProgramExpression, ProgramExpression>,
) -> Vec<(Vec<usize>, ImmutableMemoryKey)> {
    if let Some(key) = immutable_memory_key(spec, bindings, aliases) {
        return vec![(vec![clause], key)];
    }
    if spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || spec.guard().is_some()
    {
        return Vec::new();
    }
    let term = match spec.term() {
        ResourceTerm::Instance { resource, .. } => resource.as_ref(),
        term => term,
    };
    let ResourceTerm::Composite {
        name, arguments, ..
    } = term
    else {
        return Vec::new();
    };
    let Some(definition) = interface.composite_resource_definition(name) else {
        return Vec::new();
    };
    if definition.is_recursive()
        || definition.matched.is_some()
        || definition.condition.is_some()
        || !definition.children.is_empty()
        || !definition.witnesses.is_empty()
    {
        return Vec::new();
    }
    let bindings = definition
        .parameters()
        .iter()
        .zip(arguments)
        .filter_map(|(formal, actual)| {
            let value = immutable_expression(actual, bindings, aliases)?;
            if immutable_type(&value, types)? != formal.program_type() {
                return None;
            }
            Some((formal.binding_name().clone(), value))
        })
        .flat_map(|(name, value)| {
            let named = name
                .source_spelling()
                .map(|spelling| (BindingName::Named(spelling.to_owned()), value.clone()));
            std::iter::once((name, value)).chain(named)
        })
        .collect();
    definition
        .contains()
        .iter()
        .enumerate()
        .filter_map(|(child, spec)| {
            crate::instrumentation::record_deterministic_work(1);
            Some((
                vec![clause, child],
                immutable_memory_key(spec, &bindings, &BTreeMap::new())?,
            ))
        })
        .collect()
}

fn post_parameter_aliases(
    interface: &FunctionContractInterface,
    bindings: &BTreeMap<BindingName, ProgramExpression>,
) -> BTreeMap<ProgramExpression, ProgramExpression> {
    let mut result = BTreeMap::new();
    if !interface.exceptional_ensures().is_empty() {
        return result;
    }
    let mut pending = interface.contract_ensures().iter().collect::<Vec<_>>();
    while let Some(proposition) = pending.pop() {
        match proposition {
            SpecProposition::And(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            SpecProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } => {
                let (Some(left), Some(right)) = (
                    post_program_expression(left),
                    post_program_expression(right),
                ) else {
                    continue;
                };
                for (target, source) in [(&left, &right), (&right, &left)] {
                    if immutable_expression(target, bindings, &BTreeMap::new()).is_none()
                        && let Some(source) =
                            immutable_expression(source, bindings, &BTreeMap::new())
                    {
                        result.insert(target.clone(), source);
                    }
                }
            }
            _ => {}
        }
    }
    result
}

// Convert only the post-state address/read syntax represented in resource arguments.
fn post_program_expression(expression: &SpecExpression) -> Option<ProgramExpression> {
    Some(match expression {
        SpecExpression::ProgramExpression(expression) => expression.clone(),
        SpecExpression::Value(value) => ProgramExpression::Value(value.clone()),
        SpecExpression::Subobject { pointer, width } => ProgramExpression::Subobject {
            pointer: Box::new(post_program_expression(pointer)?),
            width: *width,
        },
        SpecExpression::MemoryLoad {
            point: SpecPoint::Current,
            pointer,
            value_type,
        } => ProgramExpression::TypedLoad {
            pointer: Box::new(post_program_expression(pointer)?),
            value_type: *value_type,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
        _ => return None,
    })
}

fn immutable_type(
    expression: &ProgramExpression,
    types: &BTreeMap<&BindingName, ProgramType>,
) -> Option<ProgramType> {
    match expression {
        ProgramExpression::Variable(name) => types.get(name).copied(),
        ProgramExpression::Value(value) => Some(value.program_type()),
        ProgramExpression::Cast { target_type, .. } => Some(*target_type),
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => immutable_type(pointer, types),
        ProgramExpression::AddressOf(lvalue) | ProgramExpression::CheckedObjectAddress(lvalue) => {
            match lvalue.as_ref() {
                ProgramExpression::Load(pointer) | ProgramExpression::Index(pointer, _) => {
                    immutable_type(pointer, types)
                }
                ProgramExpression::TypedLoad { value_type, .. } => value_type.pointer_to(),
                _ => None,
            }
        }
        _ => None,
    }
}

pub(super) fn invariant_condition(
    condition: Option<&SpecProposition>,
    parameters: &BTreeSet<&BindingName>,
) -> bool {
    let Some(condition) = condition else {
        return true;
    };
    let bindings = parameter_bindings(parameters.iter().copied());
    let pure = |expression: &SpecExpression| match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::ProgramExpression(expression) => {
            immutable_expression(expression, &bindings, &BTreeMap::new()).is_some()
        }
        _ => false,
    };
    let mut pending = vec![condition];
    while let Some(proposition) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            SpecProposition::And(a, b) | SpecProposition::Or(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            SpecProposition::Not(value) => pending.push(value),
            SpecProposition::Comparison { left, right, .. } if pure(left) && pure(right) => {}
            _ => return false,
        }
    }
    true
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
