//! Admission of calls whose contracts touch populations, mutexes and authority resources: which assumed contracts may update an authority population, and the member, quantity and control effects a verified or preserving contract may have.

use super::*;

/// Whether any resource the contract moves can touch a population: a
/// population authority, a mutex protocol resource, an abstract token not
/// known to be ordinary, or a family that reaches an authorized family. A contract over ordinary
/// families and memory alone has no population effect.
pub(in crate::kernel) fn contract_reaches_population(
    interface: &CFunctionContractInterface,
) -> bool {
    interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
        .any(|spec| spec_reaches_population(interface, spec))
}

pub(super) fn spec_reaches_population(
    interface: &CFunctionContractInterface,
    spec: &CResourceSpec,
) -> bool {
    if matches!(
        spec.family(),
        ResourceFamily::MutexGuard | ResourceFamily::MutexLive | ResourceFamily::MutexUse
    ) || matches!(spec.term(), CResourceTerm::PopulationAuthority { .. })
    {
        return true;
    }
    if let CResourceTerm::Token { name, .. } = spec.term()
        && (name == CResourceFact::ALLOCATION_RESOURCE_NAME
            || interface.is_ordinary_abstract_family(name))
    {
        return false;
    }
    match spec.contained_definition_name() {
        Some(name) => interface
            .composite_resource_definition(name)
            .is_none_or(|definition| definition.reaches_population()),
        None => false,
    }
}

/// Unadmitted calls cannot update an authority population. Verified effects
/// and explicitly preserving assumed interfaces are checked at their own call
/// boundaries; allocation/free use separate statement forms.
pub(super) fn authority_call_refusal() -> CRuntimeError {
    CRuntimeError::FunctionContract(AUTHORITY_ASSUMED_CALL_REFUSAL.to_string())
}

/// Why an unverified call whose contract changes a population or mutex
/// resource is refused, and the two ways to admit it.
pub(in crate::kernel) const AUTHORITY_ASSUMED_CALL_REFUSAL: &str = "the called function is not verified and its assumed contract changes a population or mutex resource; verify the function, or give it a contract that returns those resources unchanged";

pub(super) fn authority_protected_families(
    interface: &CFunctionContractInterface,
) -> BTreeSet<&str> {
    let mut protected_families = BTreeSet::new();
    for input in interface.resource_requires() {
        match input.term() {
            CResourceTerm::PopulationAuthority { protected, .. } => {
                if let CResourceTerm::Composite { name, .. } = protected.resource.term() {
                    protected_families.insert(name.as_str());
                }
            }
            CResourceTerm::Composite { name, .. } => {
                if let Some(definition) = interface.composite_resource_definition(name) {
                    for child in definition.contains() {
                        if let CResourceTerm::PopulationAuthority { protected, .. } = child.term()
                            && let CResourceTerm::Composite { name, .. } = protected.resource.term()
                        {
                            protected_families.insert(name.as_str());
                        }
                    }
                }
            }
            // A typed use reaches the authority inside its protected control
            // only by acquiring it; the helper's body is checked to change the
            // population exactly as its member clause declares.
            CResourceTerm::MutexUse {
                protected: Some(protected),
                ..
            } if input.role() == CResourceTransferRole::Borrow => {
                if let Some(name) = protected.resource.contained_definition_name()
                    && let Some(definition) = interface.composite_resource_definition(name)
                {
                    for child in definition.contains() {
                        if let CResourceTerm::PopulationAuthority { protected, .. } = child.term()
                            && let CResourceTerm::Composite { name, .. } = protected.resource.term()
                        {
                            protected_families.insert(name.as_str());
                        }
                    }
                }
            }
            _ => {}
        }
    }
    protected_families
}

/// The member effects of a locked helper: one produced or consumed member,
/// or a unit exchange between two families at one anchor, such as a retain
/// that turns a permit into a reference. Each effect names a different
/// population, so each is checked against that population's own change.
pub(super) fn locked_helper_member_effects(
    interface: &CFunctionContractInterface,
) -> Option<Vec<(bool, &CResourceSpec)>> {
    if !interface.resource_constructors().is_empty() {
        return None;
    }
    let protected_families = authority_protected_families(interface);
    let mut effects = Vec::new();
    for (produce, clauses, role) in [
        (
            false,
            interface.resource_requires(),
            CResourceTransferRole::Consume,
        ),
        (
            true,
            interface.resource_ensures(),
            CResourceTransferRole::Produce,
        ),
    ] {
        for clause in clauses {
            if clause.role() != role {
                continue;
            }
            match clause.term() {
                CResourceTerm::Composite { name, .. }
                    if protected_families.contains(name.as_str())
                        && clause.quantity() == &CResourceQuantity::One
                        && authority_member_quantity_admitted(interface, clause) =>
                {
                    effects.push((produce, clause));
                }
                _ => return None,
            }
        }
    }
    let families = effects
        .iter()
        .filter_map(|(_, spec)| match spec.term() {
            CResourceTerm::Composite { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    (!effects.is_empty() && families.len() == effects.len()).then_some(effects)
}

/// A locked helper preserves one typed use of a mutex whose protected control
/// owns population authorities, and changes those populations only by its
/// declared member effects, at most one per population. No other clause is
/// admitted. Its body is checked to make exactly those births and deaths
/// under the acquired authorities, and the caller applies them to the
/// populations whose control the mutex holds.
pub(super) fn authority_mutex_member_helper_contract(
    interface: &CFunctionContractInterface,
) -> bool {
    if !interface.resource_constructors().is_empty()
        || !matches!(
            super::super::mutexes::helper_contracts::classify(interface),
            Ok(None)
        )
    {
        return false;
    }
    let Some(effects) = locked_helper_member_effects(interface) else {
        return false;
    };
    let uses = interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .filter(|spec| spec.family() == ResourceFamily::MutexUse)
        .collect::<Vec<_>>();
    let [input, output] = uses.as_slice() else {
        return false;
    };
    let typed = |spec: &CResourceSpec| {
        matches!(
            spec.term(),
            CResourceTerm::MutexUse {
                protected: Some(_),
                ..
            }
        ) && spec.role() == CResourceTransferRole::Borrow
            && !spec.is_view()
            && spec.guard().is_none()
            && spec.mutex_authority_binding().is_some()
    };
    typed(input)
        && typed(output)
        && input.term() == output.term()
        && interface
            .resource_requires()
            .iter()
            .chain(interface.resource_ensures())
            .all(|spec| {
                effects
                    .iter()
                    .any(|(_, member)| std::ptr::eq(spec, *member))
                    || std::ptr::eq(spec, *input)
                    || std::ptr::eq(spec, *output)
            })
}

pub(super) fn population_member_requirement(member: &CResourceSpec) -> String {
    let CResourceTerm::Composite {
        name, arguments, ..
    } = member.term()
    else {
        unreachable!("checked member effect")
    };
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Variable(name) => name.as_str(),
            _ => "...",
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{name}({arguments})")
}

/// The ledger effect uses the exact owner authenticated at call admission,
/// rather than evaluating an entry field expression a second time.
pub(super) fn checked_consumed_population_member<'a>(
    interface: &CFunctionContractInterface,
    transfer: &'a CFunctionResourceTransfer,
) -> Option<&'a CResourceFact> {
    let (produce, member) = authority_member_effect(interface)?;
    if produce {
        return None;
    }
    let index = interface
        .resource_requires()
        .iter()
        .position(|spec| std::ptr::eq(spec, member))?;
    transfer
        .consumed_inputs
        .iter()
        .find(|checked| checked.section_index == Some(index))
        .map(|checked| &checked.fact)
}

/// The populations whose control a locked helper acquires. Their authority
/// stays with the caller's invocation while the control is in the mutex, so a
/// sequential call lends each to the helper in the ledger and takes it back
/// on return; no resource moves, and only the helper's checked member
/// exchanges apply.
pub(super) fn locked_helper_population(
    interface: &CFunctionContractInterface,
    transfer: &CFunctionResourceTransfer,
    callee_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<ResourceDescription>, CRuntimeError>> {
    if !authority_mutex_member_helper_contract(interface) {
        return Ok(Ok(Vec::new()));
    }
    let Some(effects) = locked_helper_member_effects(interface) else {
        return Ok(Ok(Vec::new()));
    };
    let mut populations = Vec::with_capacity(effects.len());
    for (produce, member) in effects {
        let fact = if produce {
            match evaluate_function_resource_spec(callee_entry, member, assumptions, budget)? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            }
        } else {
            let consumed = interface
                .resource_requires()
                .iter()
                .position(|spec| std::ptr::eq(spec, member))
                .and_then(|index| {
                    transfer
                        .consumed_inputs
                        .iter()
                        .find(|checked| checked.section_index == Some(index))
                });
            match consumed {
                Some(checked) => checked.fact.clone(),
                None => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "locked helper has no checked consumed member".into(),
                    )));
                }
            }
        };
        let CResource::Composite { name, arguments } = fact.resource() else {
            return Ok(Err(CRuntimeError::FunctionContract(
                "locked helper member must be a declared resource".into(),
            )));
        };
        populations.push(ResourceDescription::new(
            name.clone(),
            arguments.clone(),
            ResourceFieldSchema::new(vec![]).expect("empty schema"),
        ));
    }
    Ok(Ok(populations))
}

pub(super) fn checked_consumed_population_control<'a>(
    interface: &CFunctionContractInterface,
    transfer: &'a CFunctionResourceTransfer,
) -> Option<&'a CResourceFact> {
    let control = authority_consumed_control(interface)?;
    let index = interface
        .resource_requires()
        .iter()
        .position(|spec| std::ptr::eq(spec, control))?;
    transfer
        .consumed_inputs
        .iter()
        .find(|checked| checked.section_index == Some(index))
        .map(|checked| &checked.fact)
}

/// Select one explicit population member effect independently of ordinary
/// companion clauses. The resource planner still checks every companion;
/// the checked population exchange independently validates exact custody.
pub(super) fn authority_member_effect(
    interface: &CFunctionContractInterface,
) -> Option<(bool, &CResourceSpec)> {
    if !interface.resource_constructors().is_empty() {
        return None;
    }
    let protected_families = authority_protected_families(interface);
    let mut effect = None;
    for (produce, clauses) in [
        (false, interface.resource_requires()),
        (true, interface.resource_ensures()),
    ] {
        for clause in clauses {
            let CResourceTerm::Composite { name, .. } = clause.term() else {
                continue;
            };
            if !protected_families.contains(name.as_str())
                || clause.role()
                    != if produce {
                        CResourceTransferRole::Produce
                    } else {
                        CResourceTransferRole::Consume
                    }
            {
                continue;
            }
            if effect.is_some() || !authority_member_quantity_admitted(interface, clause) {
                return None;
            }
            effect = Some((produce, clause));
        }
    }
    effect
}

/// Admit one unit exchange, or its two-anchor counterpart: two families
/// exchange one unit each at distinct anchors. Each explicit effect keeps its
/// own authority and custody check; no global count is used as ownership.
pub(super) fn authority_exchange_effects(
    interface: &CFunctionContractInterface,
) -> Option<Vec<(bool, &CResourceSpec)>> {
    if !interface.resource_constructors().is_empty() {
        return None;
    }
    let families = authority_protected_families(interface);
    let select = |spec: &&CResourceSpec, role| {
        spec.role() == role
            && matches!(spec.term(), CResourceTerm::Composite { name, .. } if families.contains(name.as_str()))
    };
    let inputs = interface
        .resource_requires()
        .iter()
        .filter(|spec| select(spec, CResourceTransferRole::Consume))
        .collect::<Vec<_>>();
    let outputs = interface
        .resource_ensures()
        .iter()
        .filter(|spec| select(spec, CResourceTransferRole::Produce))
        .collect::<Vec<_>>();
    if inputs.len() != outputs.len() || !matches!(inputs.len(), 1 | 2) {
        return None;
    }
    fn parts(spec: &CResourceSpec) -> Option<(&str, &[CExpression])> {
        match spec.term() {
            CResourceTerm::Composite {
                name, arguments, ..
            } => Some((name.as_str(), arguments.as_slice())),
            _ => None,
        }
    }
    let pairs = if inputs.len() == 1 {
        vec![(inputs[0], outputs[0])]
    } else {
        let (left_name, left_args) = parts(inputs[0])?;
        let (right_name, right_args) = parts(inputs[1])?;
        if left_name == right_name || left_args.first()? == right_args.first()? {
            return None;
        }
        // Match each family at the opposite anchor, preserving its remaining
        // arguments (the exact object identity in the pool transfer).
        let left_output = outputs.iter().copied().find(|output| {
            parts(output).is_some_and(|(name, args)| {
                name == left_name
                    && args.first() == right_args.first()
                    && args.get(1..) == left_args.get(1..)
            })
        })?;
        let right_output = outputs.iter().copied().find(|output| {
            parts(output).is_some_and(|(name, args)| {
                name == right_name
                    && args.first() == left_args.first()
                    && args.get(1..) == right_args.get(1..)
            })
        })?;
        vec![(inputs[0], right_output), (inputs[1], left_output)]
    };
    for (input, output) in pairs {
        let (left, a) = parts(input)?;
        let (right, b) = parts(output)?;
        let same_family_move =
            left == right && a.len() >= 2 && a.len() == b.len() && a[1..] == b[1..] && a[0] != b[0];
        let family_exchange = left != right && !a.is_empty() && !b.is_empty() && a[0] == b[0];
        if !(same_family_move || family_exchange)
            || input.quantity() != &CResourceQuantity::One
            || output.quantity() != &CResourceQuantity::One
            || !authority_member_quantity_admitted(interface, input)
            || !authority_member_quantity_admitted(interface, output)
        {
            return None;
        }
        for (family, arguments) in [(left, a), (right, b)] {
            if !interface.resource_requires().iter().any(|spec| {
            if spec.role() != CResourceTransferRole::Borrow
                || spec.access() != CResourceAccessMode::Own
                || spec.quantity() != &CResourceQuantity::One
                || spec.guard().is_some()
            { return false; }
            let matches = |term: &CResourceTerm| {
                matches!(term, CResourceTerm::PopulationAuthority { protected, population_arity, .. }
                    if population_arity.map_or(arguments.len() == 1, |arity| arity == arguments.len())
                    && matches!(protected.resource.term(), CResourceTerm::Composite { name, arguments: anchor, .. }
                        if name == family && anchor.first() == arguments.first()))
            };
            if matches(spec.term()) { return true; }
            let CResourceTerm::Composite { name, arguments: wrapper_args, .. } = spec.term() else { return false; };
            let Some(definition) = interface.composite_resource_definition(name) else { return false; };
            // Initially admit the ordinary one-argument control at this anchor.
            if wrapper_args.len() != 1 || definition.parameters().len() != 1 || wrapper_args[0] != arguments[0] { return false; }
            definition.contains().iter().any(|child| {
                child.access() == CResourceAccessMode::Own
                    && child.quantity() == &CResourceQuantity::One
                    && child.guard().is_none()
                    && matches!(child.term(), CResourceTerm::PopulationAuthority { protected, population_arity, .. }
                        if population_arity.map_or(arguments.len() == 1, |arity| arity == arguments.len())
                        && matches!(protected.resource.term(), CResourceTerm::Composite { name, arguments: anchor, .. }
                            if name == family && matches!(anchor.as_slice(), [CExpression::Variable(parameter)] if parameter == definition.parameters()[0].name())))
            })
        }) { return None; }
        }
    }
    Some(
        inputs
            .into_iter()
            .map(|spec| (false, spec))
            .chain(outputs.into_iter().map(|spec| (true, spec)))
            .collect(),
    )
}

/// Two independent unit births can return their two authority controls.
/// This is a bounded composition of existing initialization contracts, not a
/// rule for arbitrary population deltas or implicit authority creation.
pub(super) fn authority_two_control_births(
    interface: &CFunctionContractInterface,
) -> Option<Vec<(bool, &CResourceSpec)>> {
    if !interface.resource_constructors().is_empty() {
        return None;
    }
    let families = authority_protected_families(interface);
    let is_member = |spec: &CResourceSpec| {
        matches!(spec.term(), CResourceTerm::Composite { name, .. }
            if families.contains(name.as_str()))
    };
    if interface
        .resource_requires()
        .iter()
        .any(|spec| is_member(spec) && spec.role() == CResourceTransferRole::Consume)
    {
        return None;
    }
    let members = interface
        .resource_ensures()
        .iter()
        .filter(|spec| is_member(spec) && spec.role() == CResourceTransferRole::Produce)
        .collect::<Vec<_>>();
    if members.len() != 2
        || members.iter().any(|member| {
            member.quantity() != &CResourceQuantity::One
                || member.instance_identity().is_some()
                || !authority_member_quantity_admitted(interface, member)
        })
    {
        return None;
    }
    // Normalize only the declared authorities of a unary control. The
    // resource planner and checked body authenticate its actual memory.
    let control = |spec: &CResourceSpec| {
        let CResourceTerm::Composite {
            name, arguments, ..
        } = spec.term()
        else {
            return None;
        };
        if spec.access() != CResourceAccessMode::Own
            || spec.quantity() != &CResourceQuantity::One
            || spec.guard().is_some()
            || !spec.resource_arguments().is_empty()
            || spec.instance_identity().is_some()
            || arguments.len() != 1
        {
            return None;
        }
        let definition = interface.composite_resource_definition(name)?;
        let [parameter] = definition.parameters() else {
            return None;
        };
        let mut scopes = Vec::new();
        for child in definition.contains() {
            let CResourceTerm::PopulationAuthority {
                protected,
                population_arity,
                ..
            } = child.term()
            else {
                continue;
            };
            let CResourceTerm::Composite {
                name,
                arguments: anchor,
                ..
            } = protected.resource.term()
            else {
                return None;
            };
            if child.access() != CResourceAccessMode::Own
                || child.quantity() != &CResourceQuantity::One
                || child.guard().is_some()
                || !child.resource_arguments().is_empty()
                || anchor.len() != 1
                || anchor[0] != c_variable(parameter.name())
            {
                return None;
            }
            scopes.push((name.clone(), *population_arity));
        }
        if scopes.is_empty() {
            return None;
        }
        scopes.sort();
        Some((arguments[0].clone(), scopes))
    };
    let inputs = interface
        .resource_requires()
        .iter()
        .filter_map(|spec| {
            (spec.role() == CResourceTransferRole::Consume)
                .then(|| control(spec))
                .flatten()
        })
        .collect::<Vec<_>>();
    let outputs = interface
        .resource_ensures()
        .iter()
        .filter_map(|spec| {
            (spec.role() == CResourceTransferRole::Produce)
                .then(|| control(spec))
                .flatten()
        })
        .collect::<Vec<_>>();
    if inputs.len() != 2 || outputs.len() != 2 || inputs[0].0 == inputs[1].0 {
        return None;
    }
    for member in &members {
        let CResourceTerm::Composite {
            name, arguments, ..
        } = member.term()
        else {
            return None;
        };
        let anchor = arguments.first()?;
        let scopes = &inputs.iter().find(|input| &input.0 == anchor)?.1;
        if !scopes.iter().any(|(family, arity)| {
            family == name && arity.map_or(arguments.len() == 1, |arity| arity == arguments.len())
        }) {
            return None;
        }
    }
    let CResourceTerm::Composite {
        arguments: left, ..
    } = members[0].term()
    else {
        return None;
    };
    let CResourceTerm::Composite {
        arguments: right, ..
    } = members[1].term()
    else {
        return None;
    };
    if left.first() == right.first() || !inputs.iter().all(|input| outputs.contains(input)) {
        return None;
    }
    // All other tracked clauses must be ordinary conserved owned borrows.
    let mut borrowed_inputs = Vec::new();
    let mut borrowed_outputs = Vec::new();
    for (incoming, clauses) in [
        (true, interface.resource_requires()),
        (false, interface.resource_ensures()),
    ] {
        for spec in clauses {
            if members.iter().any(|member| std::ptr::eq(spec, *member))
                || control(spec).is_some()
                    && spec.role()
                        == if incoming {
                            CResourceTransferRole::Consume
                        } else {
                            CResourceTransferRole::Produce
                        }
                || !matches!(
                    spec.family(),
                    ResourceFamily::Composite | ResourceFamily::PopulationAuthority
                )
            {
                continue;
            }
            if spec.role() != CResourceTransferRole::Borrow
                || spec.access() != CResourceAccessMode::Own
                || spec.quantity() != &CResourceQuantity::One
                || spec.guard().is_some()
                || !spec.resource_arguments().is_empty()
            {
                return None;
            }
            if incoming {
                borrowed_inputs.push(spec.term());
            } else {
                borrowed_outputs.push(spec.term());
            }
        }
    }
    borrowed_inputs.sort();
    borrowed_outputs.sort();
    if borrowed_inputs != borrowed_outputs {
        return None;
    }
    Some(members.into_iter().map(|member| (true, member)).collect())
}

/// A quantity exchange within one empty member family. The input partition
/// authenticates the whole consumed quantity, the return partition checks the
/// produced custody, and certification checks their net ledger change. This
/// is distinct from a unit move between populations.
pub(super) fn authority_quantity_exchange_effects(
    interface: &CFunctionContractInterface,
) -> Option<Vec<(bool, &CResourceSpec)>> {
    if !interface.resource_constructors().is_empty() {
        return None;
    }
    let families = authority_protected_families(interface);
    let select = |spec: &&CResourceSpec, role| {
        spec.role() == role
            && matches!(spec.term(), CResourceTerm::Composite { name, .. } if families.contains(name.as_str()))
    };
    let mut inputs = interface
        .resource_requires()
        .iter()
        .filter(|spec| select(spec, CResourceTransferRole::Consume));
    let input = inputs.next()?;
    if inputs.next().is_some() {
        return None;
    }
    let mut outputs = interface
        .resource_ensures()
        .iter()
        .filter(|spec| select(spec, CResourceTransferRole::Produce));
    let output = outputs.next()?;
    if outputs.next().is_some() {
        return None;
    }
    let CResourceTerm::Composite {
        name: input_name, ..
    } = input.term()
    else {
        return None;
    };
    let CResourceTerm::Composite {
        name: output_name, ..
    } = output.term()
    else {
        return None;
    };
    if input_name != output_name
        || (!matches!(input.quantity(), CResourceQuantity::Count(_))
            && !matches!(output.quantity(), CResourceQuantity::Count(_)))
        || !authority_member_quantity_admitted(interface, input)
        || !authority_member_quantity_admitted(interface, output)
        || !interface
            .composite_resource_definition(input_name)?
            .contains()
            .is_empty()
    {
        return None;
    }
    Some(vec![(false, input), (true, output)])
}

pub(super) fn authority_checked_member_effects(
    interface: &CFunctionContractInterface,
) -> Vec<(bool, &CResourceSpec)> {
    if let Some(effects) = authority_quantity_exchange_effects(interface)
        .or_else(|| authority_exchange_effects(interface))
        .or_else(|| authority_two_control_births(interface))
    {
        effects
    } else {
        authority_member_effect(interface).into_iter().collect()
    }
}

pub(super) fn authority_exchanges_member_contract(interface: &CFunctionContractInterface) -> bool {
    (authority_quantity_exchange_effects(interface).is_some()
        || authority_exchange_effects(interface).is_some())
        && authority_member_companions_admitted(interface)
}

/// Identify consumed control custody separately from the one member effect.
/// Its returned clause may use an entry spelling such as `old(p->kid)`; exact
/// evaluated population identity is checked at the resource transfer boundary.
pub(super) fn authority_consumed_control(
    interface: &CFunctionContractInterface,
) -> Option<&CResourceSpec> {
    let (produce, member) = authority_quantity_exchange_effects(interface)
        .and_then(|effects| effects.into_iter().find(|(produce, _)| !produce))
        .or_else(|| authority_member_effect(interface))?;
    if produce {
        return None;
    }
    let CResourceTerm::Composite {
        name: member_name, ..
    } = member.term()
    else {
        return None;
    };
    let mut selected = None;
    for clause in interface.resource_requires() {
        if clause.role() != CResourceTransferRole::Consume
            || clause.access() != CResourceAccessMode::Own
            || clause.quantity() != &CResourceQuantity::One
            || clause.guard().is_some()
        {
            continue;
        }
        let CResourceTerm::Composite { name, .. } = clause.term() else {
            continue;
        };
        let Some(definition) = interface.composite_resource_definition(name) else {
            continue;
        };
        if definition.contains().iter().any(|child| matches!(child.term(), CResourceTerm::PopulationAuthority { protected, .. } if matches!(protected.resource.term(), CResourceTerm::Composite { name, .. } if name == member_name))) {
            if selected.is_some() { return None; }
            selected = Some(clause);
        }
    }
    selected
}

pub(super) fn authority_returned_control(
    interface: &CFunctionContractInterface,
) -> Option<&CResourceSpec> {
    let consumed = authority_consumed_control(interface)?;
    let CResourceTerm::Composite {
        name: control_name, ..
    } = consumed.term()
    else {
        return None;
    };
    let mut returned = interface.resource_ensures().iter().filter(|clause| matches!(clause.term(), CResourceTerm::Composite { name, .. } if name == control_name));
    let clause = returned.next()?;
    if returned.next().is_some()
        || clause.role() != CResourceTransferRole::Produce
        || clause.access() != CResourceAccessMode::Own
        || clause.quantity() != &CResourceQuantity::One
        || !clause.resource_arguments().is_empty()
    {
        return None;
    }
    Some(clause)
}

/// Every mutex resource in this contract is borrowed whole and returned
/// unchanged: a typed `mutex_use` share, a guard or a lifetime. The contract
/// is no acquiring or releasing helper. A body that locks through a borrowed
/// share is checked at return by `check_acquired_control_member_effects`; a
/// body holding only a borrowed guard or lifetime cannot reacquire a deposited
/// control, and returning the same mutex resources leaves the mutex state as it
/// was. Preserving its other resources therefore changes no population the
/// caller holds.
pub(super) fn authority_borrows_only_mutex_resources(
    interface: &CFunctionContractInterface,
) -> bool {
    matches!(
        super::super::mutexes::helper_contracts::classify(interface),
        Ok(None)
    ) && interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .filter(|spec| spec_contains_mutex_authority(interface, spec))
        .all(|spec| {
            matches!(
                spec.family(),
                ResourceFamily::MutexUse | ResourceFamily::MutexGuard | ResourceFamily::MutexLive
            ) && spec.role() == CResourceTransferRole::Borrow
                && spec.access() == CResourceAccessMode::Own
                && spec.quantity() == &CResourceQuantity::One
                && spec.guard().is_none()
                && !spec.is_view()
        })
}

pub(super) fn authority_preserves_resource_contract(
    interface: &CFunctionContractInterface,
) -> bool {
    if !interface.resource_constructors().is_empty()
        || (interface
            .resource_requires()
            .iter()
            .chain(interface.resource_ensures())
            .any(|spec| spec_contains_mutex_authority(interface, spec))
            && !authority_borrows_only_mutex_resources(interface))
    {
        return false;
    }
    let tracked = |spec: &&CResourceSpec| {
        matches!(
            spec.family(),
            ResourceFamily::Composite | ResourceFamily::PopulationAuthority
        )
    };
    let protected = authority_protected_families(interface);
    let admitted = |spec: &&CResourceSpec| {
        spec.role() == CResourceTransferRole::Borrow
            && spec.access() == CResourceAccessMode::Own
            && (spec.quantity() == &CResourceQuantity::One
                || matches!(spec.term(), CResourceTerm::Composite { name, .. }
                    if protected.contains(name.as_str())
                        && authority_member_quantity_admitted(interface, spec)))
            && spec.guard().is_none()
            && spec.resource_arguments().is_empty()
    };
    let mut inputs = interface
        .resource_requires()
        .iter()
        .filter(tracked)
        .collect::<Vec<_>>();
    let mut outputs = interface
        .resource_ensures()
        .iter()
        .filter(tracked)
        .collect::<Vec<_>>();
    if !inputs.iter().all(admitted) || !outputs.iter().all(admitted) {
        return false;
    }
    inputs.sort_by_key(|spec| spec.term());
    outputs.sort_by_key(|spec| spec.term());
    inputs.len() == outputs.len()
        && inputs
            .iter()
            .zip(outputs)
            .all(|(left, right)| left.term() == right.term() && left.quantity() == right.quantity())
}

/// An assumed contract may preserve a ledger, but it has no body certificate
/// justifying population births or spends. Named occurrences must be borrowed
/// and returned with exactly the same identity and description as well.
pub(in crate::kernel) fn authority_preserves_assumed_resource_contract(
    interface: &CFunctionContractInterface,
) -> bool {
    if !authority_preserves_resource_contract(interface)
        || authority_protected_families(interface).is_empty()
            && !interface
                .resource_requires()
                .iter()
                .any(|spec| spec.family() == ResourceFamily::Instance)
    {
        return false;
    }
    let named = |spec: &&CResourceSpec| spec.family() == ResourceFamily::Instance;
    let mut inputs = interface
        .resource_requires()
        .iter()
        .filter(named)
        .collect::<Vec<_>>();
    let mut outputs = interface
        .resource_ensures()
        .iter()
        .filter(named)
        .collect::<Vec<_>>();
    let admitted = |spec: &&CResourceSpec| {
        spec.role() == CResourceTransferRole::Borrow
            && spec.access() == CResourceAccessMode::Own
            && spec.quantity() == &CResourceQuantity::One
            && spec.guard().is_none()
    };
    if !inputs.iter().all(admitted) || !outputs.iter().all(admitted) {
        return false;
    }
    inputs.sort_by_key(|spec| spec.term());
    outputs.sort_by_key(|spec| spec.term());
    inputs.len() == outputs.len()
        && inputs.iter().zip(outputs).all(|(input, output)| {
            input.term() == output.term()
                && input.resource_arguments() == output.resource_arguments()
        })
}

/// Direct population-like companions remain conserved. A control wrapper's
/// own authority is moved by the checked call boundary; named instances and
/// memory clauses retain their ordinary resource validation.
pub(super) fn authority_member_companions_admitted(interface: &CFunctionContractInterface) -> bool {
    let effects = authority_checked_member_effects(interface);
    let Some((_, member)) = effects.first() else {
        return false;
    };
    let CResourceTerm::Composite {
        name: member_name, ..
    } = member.term()
    else {
        return false;
    };
    let is_control = |spec: &CResourceSpec| {
        let CResourceTerm::Composite { name, .. } = spec.term() else {
            return false;
        };
        spec.access() == CResourceAccessMode::Own && spec.quantity() == &CResourceQuantity::One && spec.resource_arguments().is_empty() && interface.composite_resource_definition(name).is_some_and(|definition| definition.contains().iter().any(|child| matches!(child.term(), CResourceTerm::PopulationAuthority { protected, .. } if matches!(protected.resource.term(), CResourceTerm::Composite { name, .. } if name == member_name))))
    };
    // The checked member exchange transfers its existing body resources.
    // Admitting a declared child here changes no child-population total; the
    // ordinary resource planner and verified body check the exact arguments.
    let is_member_body_transfer = |input: bool, spec: &CResourceSpec| {
        let CResourceTerm::Composite {
            name: child_name, ..
        } = spec.term()
        else {
            return false;
        };
        spec.access() == CResourceAccessMode::Own
            && spec.quantity() == &CResourceQuantity::One
            && spec.guard().is_none()
            && spec.resource_arguments().is_empty()
            && spec.role() == if input { CResourceTransferRole::Consume } else { CResourceTransferRole::Produce }
            && effects.iter().any(|(produce, member)| {
                if *produce != input { return false; }
                let CResourceTerm::Composite { name, .. } = member.term() else { return false; };
                interface.composite_resource_definition(name).is_some_and(|definition| {
                    definition.contains().iter().any(|child| {
                        child.access() == CResourceAccessMode::Own
                            && child.quantity() == &CResourceQuantity::One
                            && child.guard().is_none()
                            && child.resource_arguments().is_empty()
                            && matches!(child.term(), CResourceTerm::Composite { name, .. } if name == child_name)
                    })
                })
            })
    };
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for (input, clauses) in [
        (true, interface.resource_requires()),
        (false, interface.resource_ensures()),
    ] {
        for spec in clauses {
            if effects
                .iter()
                .any(|(_, member)| std::ptr::eq(spec, *member))
                || !matches!(
                    spec.family(),
                    ResourceFamily::Composite | ResourceFamily::PopulationAuthority
                )
            {
                continue;
            }
            if is_member_body_transfer(input, spec) {
                continue;
            }
            if is_control(spec) && spec.role() != CResourceTransferRole::Borrow {
                // A single-member effect or same-population quantity exchange
                // can replace control. A unit move borrows its authorities.
                if (effects.len() != 1 && authority_quantity_exchange_effects(interface).is_none())
                    || (input && spec.guard().is_some())
                {
                    return false;
                }
                continue;
            }
            if spec.role() != CResourceTransferRole::Borrow
                || spec.access() != CResourceAccessMode::Own
                || spec.quantity() != &CResourceQuantity::One
                || spec.guard().is_some()
                || !spec.resource_arguments().is_empty()
            {
                return false;
            }
            if input {
                inputs.push(spec);
            } else {
                outputs.push(spec);
            }
        }
    }
    inputs.sort_by_key(|spec| spec.term());
    outputs.sort_by_key(|spec| spec.term());
    inputs.len() == outputs.len()
        && inputs
            .iter()
            .zip(outputs)
            .all(|(left, right)| left.term() == right.term())
}

pub(super) fn authority_member_quantity_admitted(
    interface: &CFunctionContractInterface,
    member: &CResourceSpec,
) -> bool {
    if member.access() != CResourceAccessMode::Own
        || member.guard().is_some()
        || !member.resource_arguments().is_empty()
    {
        return false;
    }
    if member.quantity() == &CResourceQuantity::One {
        return true;
    }
    let CResourceTerm::Composite { name, .. } = member.term() else {
        return false;
    };
    // Several identical members cannot each own the same private body.
    matches!(member.quantity(), CResourceQuantity::Count(_))
        && interface
            .composite_resource_definition(name)
            .is_some_and(|definition| definition.contains().is_empty())
}

pub(super) fn authority_consumes_member_contract(interface: &CFunctionContractInterface) -> bool {
    authority_member_effect(interface).is_some_and(|(produce, _)| !produce)
        && authority_member_companions_admitted(interface)
}

/// Standalone claim certification must check wildcard and paired consumptions even
/// when its only output claim is the borrowed authority. Merely retaining
/// that output does not establish the consumed member's ledger transition.
pub(in crate::kernel) fn check_wildcard_consumption_at_return(
    entry: &CState,
    exit: &CState,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(), CRuntimeError>> {
    if authority_quantity_exchange_effects(interface).is_some()
        && authority_member_companions_admitted(interface)
    {
        return check_quantity_exchange_at_return(entry, exit, interface, assumptions, budget);
    }
    if !(authority_consumes_member_contract(interface)
        || authority_exchanges_member_contract(interface))
    {
        return Ok(Ok(()));
    }
    for (_, member) in authority_checked_member_effects(interface)
        .into_iter()
        .filter(|(produce, _)| !produce)
    {
        let paired = authority_exchange_effects(interface).is_some();
        let CResourceTerm::Composite {
            name: member_name, ..
        } = member.term()
        else {
            continue;
        };
        // A member argument may read a field inside a folded entry instance,
        // which this exit check cannot open. The proof's own import of that
        // family then identifies the governed population, when it is unique.
        let (description, quantity) = match evaluate_function_resource_spec_with_entry(
            entry,
            entry,
            member,
            assumptions,
            budget,
        )? {
            Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity)) => (
                ResourceDescription::new(
                    name.clone(),
                    arguments,
                    ResourceFieldSchema::new(vec![]).expect("empty schema"),
                ),
                quantity,
            ),
            Ok(_) => continue,
            Err(error) => {
                let imported = exit
                    .population_effects
                    .creation
                    .as_ref()
                    .map(|events| events.imported_populations_of_family(member_name))
                    .unwrap_or_default();
                let (CResourceQuantity::One, [description]) =
                    (member.quantity(), imported.as_slice())
                else {
                    return Ok(Err(error));
                };
                (description.clone(), Box::new(Bitvector32Term::Constant(1)))
            }
        };
        // A declared consumption under an authority this proof holds is a
        // death the caller applies, so the body must have recorded it with a
        // checked spend. Otherwise a returned control could state its counter
        // equation before a death the caller then applies.
        let governed = exit
            .population_effects
            .creation
            .as_ref()
            .and_then(|events| events.governing_authority(&description))
            .is_some();
        if !governed && !paired {
            continue;
        }
        // A population entered by a typed lock in this body is checked by
        // `check_acquired_control_member_effects`, which reads its change
        // after unlock has returned the authority to the escrow.
        if let (Some(before), Some(after)) = (
            entry.population_effects.creation.as_ref(),
            exit.population_effects.creation.as_ref(),
        ) && after.opaque_imports_since(before).contains(&description)
        {
            continue;
        }
        let zero = |term: &Bitvector32Term| {
            term.as_const() == Some(0)
                || crate::kernel::quantity_condition_holds(
                    assumptions,
                    ConditionTerm::Bitvector32Equal(
                        Box::new(term.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                )
        };
        let delta = exit
            .population_effects
            .creation
            .as_ref()
            .and_then(|events| events.imported_member_delta_since_entry(&description));
        let consumed = (zero(&quantity) && delta.as_ref().is_none_or(|(_, actual)| zero(actual)))
            || delta.is_some_and(|(produce, actual_quantity)| {
                !produce
                    && (actual_quantity == *quantity
                        || crate::kernel::quantity_condition_holds(
                            assumptions,
                            ConditionTerm::Bitvector32Equal(
                                Box::new(actual_quantity),
                                quantity.clone(),
                            ),
                        ))
            });
        if !consumed {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "Requires consumes {}",
                population_member_requirement(member)
            ))));
        }
    }
    Ok(Ok(()))
}

/// Check the net effect of a same-population quantity exchange. Both custody
/// partitions are checked separately; this compares only the authenticated
/// ledger delta and never turns a population count into owned members.
pub(super) fn check_quantity_exchange_at_return(
    entry: &CState,
    exit: &CState,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(), CRuntimeError>> {
    let effects = authority_quantity_exchange_effects(interface).expect("quantity exchange");
    let Some(values) = interface
        .parameters()
        .iter()
        .map(|parameter| entry.locals().get(parameter.name()).cloned())
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "quantity exchange lost its entry argument bindings".into(),
        )));
    };
    // A function exit has discarded its C locals. Use the same contract-only
    // parameter views as ordinary boundary evaluation, retaining the entry
    // memory for old(...) and never treating these read views as custody.
    let entry_view = with_contract_interface_argument_views(entry, interface, &values);
    let exit_view = with_contract_interface_argument_views(exit, interface, &values);
    let mut members = Vec::with_capacity(2);
    for (produce, spec) in effects {
        let state = if produce { &exit_view } else { &entry_view };
        match evaluate_function_resource_spec_with_entry(
            &entry_view,
            state,
            spec,
            assumptions,
            budget,
        )? {
            Ok(fact) => members.push(fact),
            Err(error) => return Ok(Err(error)),
        }
    }
    if let Some(input) = entry
        .resources()
        .directly_supporting_fact(&members[0], assumptions)
    {
        members[0] = CResourceFact::own_quantity(
            input.resource().clone(),
            members[0]
                .owned_quantity_term()
                .expect("owned input")
                .clone(),
        );
    }
    let [input, output] = members.as_slice() else {
        unreachable!("one input and one output")
    };
    let matches = match (input, output) {
        (
            CResourceFact::Own(CResource::Composite { name, arguments }, consumed),
            CResourceFact::Own(
                CResource::Composite {
                    name: output_name,
                    arguments: output_arguments,
                },
                produced,
            ),
        ) if name == output_name
            && arguments.len() == output_arguments.len()
            && arguments
                .iter()
                .zip(output_arguments.iter())
                .all(|(left, right)| {
                    crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                }) =>
        {
            let description = ResourceDescription::new(
                name.clone(),
                arguments.clone(),
                ResourceFieldSchema::new(vec![]).expect("empty schema"),
            );
            exit.population_effects
                .creation
                .as_ref()
                .and_then(|events| events.imported_member_delta_since_entry(&description))
                .is_some_and(|(produce, actual)| {
                    let actual = if produce {
                        actual
                    } else {
                        Bitvector32Term::Subtract(
                            Box::new(Bitvector32Term::Constant(0)),
                            Box::new(actual),
                        )
                    };
                    crate::kernel::quantity_condition_holds(
                        assumptions,
                        ConditionTerm::Bitvector32Equal(
                            Box::new(actual),
                            Box::new(Bitvector32Term::Subtract(
                                Box::new((**produced).clone()),
                                Box::new((**consumed).clone()),
                            )),
                        ),
                    )
                })
        }
        _ => false,
    };
    if matches {
        Ok(Ok(()))
    } else {
        Ok(Err(CRuntimeError::FunctionContract(
            "consumes/produces member quantities do not establish the declared net population change".into()
        )))
    }
}

pub(super) fn authority_produces_member_contract(interface: &CFunctionContractInterface) -> bool {
    (authority_member_effect(interface).is_some_and(|(produce, _)| produce)
        && authority_member_companions_admitted(interface))
        || authority_two_control_births(interface).is_some()
}

pub(super) fn authority_final_release_contract(interface: &CFunctionContractInterface) -> bool {
    authority_consumes_member_contract(interface)
        && authority_consumed_control(interface).is_some()
        && authority_returned_control(interface).is_none()
}

pub(super) fn authority_conditional_release_contract(
    interface: &CFunctionContractInterface,
) -> bool {
    authority_returned_control(interface).is_some_and(|returned| returned.guard().is_some())
}

pub(super) fn authority_release_retires_control(
    entry: &CState,
    post: &CState,
    interface: &CFunctionContractInterface,
    checked_control: Option<&CResourceFact>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<bool, CRuntimeError>> {
    if authority_final_release_contract(interface) {
        return Ok(Ok(true));
    }
    if !authority_conditional_release_contract(interface) {
        return Ok(Ok(false));
    }
    let mut named_views = Vec::new();
    for named in interface
        .resource_requires()
        .iter()
        .filter(|spec| spec.is_instance())
    {
        let fact = match evaluate_function_resource_spec_with_entry(
            entry,
            entry,
            named,
            assumptions,
            budget,
        )? {
            Ok(fact) => fact,
            Err(error) => return Ok(Err(error)),
        };
        let Some(owned) = entry
            .resources()
            .directly_supporting_fact(&fact, assumptions)
            .filter(|fact| fact.is_own())
        else {
            continue;
        };
        if let Some((ranges, _)) = matched_instance_body_ownership(
            owned,
            interface.composite_resource_definitions(),
            entry,
            assumptions,
        ) {
            named_views.extend(
                ranges
                    .into_iter()
                    .map(|range| CResourceFact::View(CResource::Memory(range))),
            );
        }
    }
    let argument_entry = entry
        .clone()
        .with_resource_context(entry.resources().clone().unchecked_with_facts(named_views));
    let control = authority_consumed_control(interface).expect("checked conditional input control");
    let selected = if let Some(checked) = checked_control {
        checked.clone()
    } else {
        match evaluate_function_resource_spec_with_entry(
            &argument_entry,
            &argument_entry,
            control,
            assumptions,
            budget,
        )? {
            Ok(selected) => selected,
            Err(error) => return Ok(Err(error)),
        }
    };
    let frontier = ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(selected);
    let read_entry = match checked_contract_control_read_state(
        &argument_entry,
        &frontier,
        interface,
        assumptions,
    ) {
        Ok(read_entry) => read_entry,
        Err(error) => return Ok(Err(error)),
    };
    resource_spec_guard_is_active(
        &read_entry,
        post,
        authority_returned_control(interface).expect("checked conditional control"),
        assumptions,
        budget,
    )
    .map(|result| result.map(|returned| !returned))
}

/// An acquiring or releasing helper moves one guard and the protected state
/// between its caller and the mutex. Its standalone body cannot open an
/// acquired authority-bearing state, so it changes no population; the caller
/// applies the checked runtime exchange. Any other clause leaves this subset.
pub(super) fn authority_mutex_helper_contract(interface: &CFunctionContractInterface) -> bool {
    let Ok(Some(helper)) = super::super::mutexes::helper_contracts::classify(interface) else {
        return false;
    };
    let mut accesses = 0;
    let mut guards = 0;
    let mut payloads = 0;
    for spec in interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
    {
        if spec.term() == helper.access.term()
            && spec.role() == helper.access.role()
            && spec.mutex_authority_binding() == helper.access.mutex_authority_binding()
        {
            accesses += 1;
        } else if spec == &helper.guard {
            guards += 1;
        } else if helper.payload.as_ref() == Some(spec) {
            payloads += 1;
        } else {
            return false;
        }
    }
    accesses == 2 && guards == 1 && payloads == usize::from(helper.payload.is_some())
}

pub(super) fn authority_supports_resource_contract(interface: &CFunctionContractInterface) -> bool {
    if interface.resource_constructors().is_empty()
        && (authority_mutex_helper_contract(interface)
            || authority_mutex_member_helper_contract(interface))
    {
        return true;
    }
    if !interface.resource_constructors().is_empty() {
        return false;
    }
    if interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .any(|spec| spec_contains_mutex_authority(interface, spec))
    {
        return authority_preserves_resource_contract(interface);
    }
    authority_preserves_resource_contract(interface)
        || authority_consumes_member_contract(interface)
        || authority_produces_member_contract(interface)
        || authority_final_release_contract(interface)
        || authority_exchanges_member_contract(interface)
}
