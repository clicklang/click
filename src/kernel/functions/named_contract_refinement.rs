//! Checking that a function refines a named contract: the refinement theorem's statement, the entry and implementation states, and the resource instances both sides are compared on.

use super::*;

/// Prints the explicit refinement theorem that automatic formation could not
/// replace, with every slot filled from the two declarations the check read.
///
/// The skeleton is the expand affordance of the automatic route. It is built
/// from the same `CFunctionContract` and `CFunction` interfaces the check
/// uses — the target's proof parameters, the implementation's binders, and
/// the implementation's C parameter list — so the printed obligation cannot
/// drift from the one that was refused. A target with no proof parameters
/// gets the `unfold(Name)` form, which is the route that already exists.
///
/// `declared_parameter_spellings` carries, per parameter position, the C
/// spelling the caller's source declaration uses where this interface cannot
/// reconstruct it: an aggregate pointer is a layout here, not a struct tag,
/// so `struct node*` would print as the pointer type it is modeled by. The
/// caller supplies the tag rather than the kernel storing one; a position
/// without a supplied spelling keeps this interface's own.
pub(in crate::kernel) fn named_contract_refinement_theorem_skeleton(
    contract: &CFunctionContract,
    function: &CFunction,
    declared_parameter_spellings: &[Option<String>],
) -> String {
    let theorem = format!(
        "{}_is_{}",
        function.name(),
        snake_case_contract_name(contract.name())
    );
    let parameters = function
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let spelling = declared_parameter_spellings
                .get(index)
                .and_then(Option::as_deref)
                .map(str::to_string)
                .unwrap_or_else(|| c_parameter_type_spelling(parameter));
            format!("{spelling} {}", parameter.name())
        })
        .collect::<Vec<_>>()
        .join(", ");
    let target_binders = declared_instance_binder_names(&[contract.proof_parameters()]);
    if target_binders.is_empty() {
        return format!(
            "theorem {theorem}() {{\n    \
             ensures {contract}(&{function}) by {{\n        \
             unfold({contract});\n        \
             simp();\n    \
             }}\n\
             }}",
            contract = contract.name(),
            function = function.name(),
        );
    }
    let implementation_binders = declared_instance_binder_names(&[
        function.resource_requires(),
        function.resource_ensures(),
    ]);
    let introduced =
        introduced_instance_names(target_binders.len().max(implementation_binders.len()));
    let map = |binders: &[String]| {
        binders
            .iter()
            .zip(&introduced)
            .map(|(binder, name)| format!("{binder}: {name}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| parameter.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "theorem {theorem}() executes {function}({parameters}) {{\n    \
         ensures {contract}(&{function}) as {{ {target} }} by {{\n        \
         step({function}({arguments}), {{ {implementation} }});\n        \
         simp();\n    \
         }}\n\
         }}",
        contract = contract.name(),
        function = function.name(),
        target = map(&target_binders),
        implementation = map(&implementation_binders),
    )
}

/// The binder spellings a declaration introduces, in declaration order, once
/// per identity.
pub(super) fn declared_instance_binder_names(specs: &[&[CResourceSpec]]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if seen.insert(identity) {
            names.push(spec.instance_binder().unwrap_or_default().to_string());
        }
    }
    names
}

/// Fresh names for the instances the theorem introduces. One instance is
/// `r`; several are numbered so the two maps can name the same instance.
pub(super) fn introduced_instance_names(count: usize) -> Vec<String> {
    if count == 1 {
        return vec!["r".to_string()];
    }
    (1..=count).map(|index| format!("r{index}")).collect()
}

pub(super) fn snake_case_contract_name(name: &str) -> String {
    let mut snake = String::with_capacity(name.len() + 4);
    for (index, character) in name.char_indices() {
        if character.is_uppercase() && index != 0 {
            snake.push('_');
        }
        snake.extend(character.to_lowercase());
    }
    snake
}

/// The C0 spelling of a parameter's declared type.
///
/// Struct tags are not part of the kernel interface: an aggregate parameter
/// keeps its layout, not the tag its source wrote, so a pointer to one is
/// spelled by its pointer type. The skeleton is source the user edits, and
/// this is the one slot they may have to correct.
pub(super) fn c_parameter_type_spelling(parameter: &CParameter) -> String {
    let base = c_type_spelling(parameter.c_type());
    if parameter.pointee_is_constant() {
        format!("const {base}")
    } else {
        base.to_string()
    }
}

/// The C0 spelling of a kernel C type, for a diagnostic that has to say what
/// type a value had. An aggregate pointer is spelled by its pointer type, as
/// [`c_parameter_type_spelling`] explains.
pub(crate) fn c_type_spelling(c_type: CType) -> &'static str {
    match c_type {
        CType::Void => "void",
        CType::Bool => "bool",
        CType::VoidPointer => "void*",
        CType::VoidPointerPointer => "void**",
        CType::Int8 => "int8",
        CType::Int16 => "int16",
        CType::Int32 => "int32",
        CType::UInt8 => "uint8",
        CType::UInt16 => "uint16",
        CType::UInt32 => "uint32",
        CType::Int64 => "int64",
        CType::UInt64 => "uint64",
        CType::Int128 => "int128",
        CType::UInt128 => "uint128",
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        CType::Int8Pointer => "int8*",
        CType::Int16Pointer => "int16*",
        CType::UInt16Pointer => "uint16*",
        CType::Int32Pointer => "int32*",
        CType::UInt8Pointer => "uint8*",
        CType::UInt32Pointer => "uint32*",
        CType::Int64Pointer => "int64*",
        CType::Int128Pointer => "int128*",
        CType::UInt64Pointer => "uint64*",
        CType::UInt128Pointer => "uint128*",
        CType::Float32Pointer => "float32*",
        CType::Float64Pointer => "float64*",
        CType::Int8PointerPointer => "int8**",
        CType::Int16PointerPointer => "int16**",
        CType::UInt16PointerPointer => "uint16**",
        CType::Int32PointerPointer => "int32**",
        CType::UInt8PointerPointer => "uint8**",
        CType::UInt32PointerPointer => "uint32**",
        CType::Int64PointerPointer => "int64**",
        CType::Int128PointerPointer => "int128**",
        CType::UInt64PointerPointer => "uint64**",
        CType::UInt128PointerPointer => "uint128**",
        CType::Float32PointerPointer => "float32**",
        CType::Float64PointerPointer => "float64**",
        CType::FunctionPointer(_) => "void (*)()",
        CType::Int8Array(_) => "int8*",
        CType::Int16Array(_) => "int16*",
        CType::Int32Array(_) => "int32*",
        CType::UInt8Array(_) => "uint8*",
        CType::UInt16Array(_) => "uint16*",
        CType::UInt32Array(_) => "uint32*",
        CType::Int64Array(_) => "int64*",
        CType::Int128Array(_) => "int128*",
        CType::UInt64Array(_) => "uint64*",
        CType::UInt128Array(_) => "uint128*",
        CType::Float32Array(_) => "float32*",
        CType::Float64Array(_) => "float64*",
        CType::PointerArray(element, _) => element.decayed_type_spelling(),
    }
}

/// Proves behavioral callback refinement. Exact matching remains the fast
/// path. The semantic path checks framed memory, abstract-token, and folded
/// composite resource transitions and effect containment, instantiates both
/// interfaces with the same symbolic arguments, then checks preconditions
/// contravariantly and postconditions covariantly. Concrete resource needs and
/// mutable ranges may be narrower than the named contract's upper bounds.
/// Stateful refinement is deliberately limited to memory propositions backed
/// by a nonempty resource transition and unguarded named mutable footprint.
pub(in crate::kernel) fn function_refines_named_contract(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.exactly_matches(function) {
        return Ok(true);
    }
    if !contract.has_same_predicate_unfoldings(function) {
        return Ok(false);
    }
    let Some(context) = prepare_automatic_contract_refinement_context(contract, function, budget)
    else {
        return Ok(false);
    };
    function_refines_named_contract_in_case(&context, &[], &BTreeSet::new(), false, None, budget)
}

/// Whether `source`, a named contract a fact fixed, implements `contract`.
/// It is the automatic route of an explicit contract-to-contract refinement
/// theorem, with the source's value parameters bound to the fact's values.
/// The values are the caller's terms, so the caller's facts about them hold.
pub(super) fn contract_refines_contract(
    contract: &CFunctionContract,
    source: &CFunctionContract,
    caller_facts: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.name() == source.name() && contract.value_arguments() == source.value_arguments() {
        return Ok(true);
    }
    let target = contract.interface();
    let implementation = source.interface();
    if !source.proof_parameters().is_empty()
        || target.predicate_unfoldings() != implementation.predicate_unfoldings()
        || !target.has_compatible_signature_and_composite_vocabulary(implementation)
    {
        return Ok(false);
    }
    let Some(mut context) =
        contract_refinement_context_for_interface(contract, source.name(), implementation, budget)
    else {
        return Ok(false);
    };
    context.function_value_arguments = source.value_arguments().to_vec();
    function_refines_named_contract_in_case(
        &context,
        &[],
        &BTreeSet::new(),
        false,
        Some(caller_facts),
        budget,
    )
}

pub(in crate::kernel) fn prepare_function_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_resource_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

/// The concrete-pointer formation route's context.
///
/// It differs from the explicit route only in admitting a target that
/// declares proof parameters. The instances those parameters stand for are
/// introduced by [`function_refines_named_contract_in_case`], and only when
/// the binding between the two declarations is forced.
pub(super) fn prepare_automatic_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_composite_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

pub(super) fn contract_refinement_context_for_checked_interfaces(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    contract_refinement_context_for_interface(
        contract,
        function.name(),
        function.contract_interface(),
        budget,
    )
}

pub(in crate::kernel) fn contract_refinement_context_for_interface(
    contract: &CFunctionContract,
    function_name: &str,
    function_interface: &CFunctionContractInterface,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    let mut argument_values = Vec::with_capacity(function_interface.parameters().len());
    for parameter in function_interface.parameters() {
        let variable = budget.allocate_kernel_variable().ok()?;
        argument_values.push(symbolic_call_result(parameter.c_type(), variable));
    }
    let result_variable = budget.allocate_kernel_variable().ok()?;
    // A contract not fixed by a fact holds for arbitrary values of its value
    // parameters.
    let contract =
        if contract.value_arguments().len() == contract.interface().value_parameters().len() {
            contract.clone()
        } else {
            let mut values = Vec::new();
            for parameter in contract.interface().value_parameters() {
                let variable = budget.allocate_kernel_variable().ok()?;
                values.push(symbolic_call_result(parameter.c_type(), variable));
            }
            contract.instantiated(&values)?
        };
    let pointer_type = contract.function_pointer_type();
    Some(CFunctionContractRefinementContext {
        contract,
        function_interface: function_interface.clone(),
        function_name: function_name.to_string(),
        pointer: CPointerValue::new(
            Pointer {
                block: PointerBlock::Function(function_name.to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            pointer_type,
        ),
        source_contract: None,
        function_value_arguments: Vec::new(),
        argument_values,
        result_variable,
        next_kernel_variable: budget.next_kernel_variable(),
    })
}

pub(in crate::kernel) fn function_contract_refinement_entry_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    let mut state = with_contract_interface_argument_views(
        &CState::new().with_population_creation_tracking(),
        &context.contract.interface,
        &context.argument_values,
    );
    for (parameter, value) in context
        .contract
        .interface
        .value_parameters()
        .iter()
        .zip(context.contract.value_arguments())
    {
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            false,
            false,
            false,
            false,
        );
    }
    state
}

/// The implementation side's entry frame: the shared arguments, and the
/// values its fact fixed for its own value parameters.
pub(super) fn function_contract_refinement_implementation_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    let mut state = with_contract_interface_argument_views(
        &CState::new().with_population_creation_tracking(),
        &context.function_interface,
        &context.argument_values,
    );
    for (parameter, value) in context
        .function_interface
        .value_parameters()
        .iter()
        .zip(&context.function_value_arguments)
    {
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            false,
            false,
            false,
            false,
        );
    }
    state
}

pub(in crate::kernel) fn prepare_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    let target = context.contract.interface();
    let source = &context.function_interface;
    // The theorem's obligation states the normal outcome only; a source that
    // may throw owes its exceptional guarantees too, which it does not
    // carry yet, so that refinement is left to the automatic route.
    if !source.exceptional_signature().is_empty() {
        return None;
    }
    let mut budget = ExecutionBudget::continuing_from(context.next_kernel_variable);
    let entry = function_contract_refinement_entry_state(context);
    let source_entry = function_contract_refinement_implementation_state(context);
    let mut assumptions = PureFactContext::new();
    if !assume_contract_propositions(
        &entry,
        &entry,
        target.contract_requires(),
        &mut assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    // A single conservative post memory covers every possible source write.
    // This does not enumerate guard combinations or assert that a guarded
    // write happened. Resource/effect containment is checked independently.
    let ranges = evaluate_contract_mutable_ranges_for_interface(
        source,
        &source_entry,
        &assumptions,
        &mut budget,
        false,
    )
    .ok()??;
    let memory = entry.memory().clone().with_call_memory_havoc(
        budget.allocate_kernel_variable().ok()?,
        &ranges,
        &assumptions,
        None,
    );
    let result = symbolic_call_result(source.return_type(), context.result_variable);
    let mut post = entry.clone().with_memory(memory.clone());
    let mut source_post = source_entry.clone().with_memory(memory);
    if source.return_type() != CType::Void {
        set_contract_result(&mut post, target, result.clone());
        set_contract_result(&mut source_post, source, result);
    }
    if !compatible_resource_and_effect_interfaces(
        target,
        source,
        &entry,
        &source_entry,
        &post,
        &source_post,
        &assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    fn conjunction(items: Vec<Proposition>) -> Proposition {
        items
            .into_iter()
            .reduce(|a, b| Proposition::And(Box::new(a), Box::new(b)))
            .unwrap_or(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            ))
    }
    fn lower(
        interface: &CFunctionContractInterface,
        specs: &[SpecProposition],
        state: &CState,
        entry: &CState,
        budget: &mut ExecutionBudget,
    ) -> Option<Proposition> {
        let definitions = interface
            .predicate_unfoldings()
            .iter()
            .map(|definition| (definition.body(), definition.predicate()))
            .collect::<BTreeMap<_, _>>();
        let mut propositions = Vec::new();
        for spec in specs {
            let spec = definitions.get(spec).copied().unwrap_or(spec);
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                spec,
                Some(entry),
                &PureFactContext::new(),
                budget,
            )
            .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            // Lowering facts name reads and other definitional intermediates;
            // they are not clauses of either callback contract. Both sides
            // use the same kernel load identities in these fixed memories.
            propositions.extend(
                path.obligations
                    .iter()
                    .map(|obligation| obligation.proposition().clone()),
            );
            propositions.push(path.proposition.clone());
        }
        Some(conjunction(propositions))
    }
    let target_requires = lower(
        target,
        target.contract_requires(),
        &entry,
        &entry,
        &mut budget,
    )?;
    let source_requires = lower(
        source,
        source.contract_requires(),
        &source_entry,
        &source_entry,
        &mut budget,
    )?;
    let source_ensures = lower(
        source,
        source.contract_ensures(),
        &source_post,
        &source_entry,
        &mut budget,
    )?;
    let target_ensures = lower(
        target,
        target.contract_ensures(),
        &post,
        &entry,
        &mut budget,
    )?;
    let proposition = Proposition::Implies(
        Box::new(target_requires),
        Box::new(Proposition::And(
            Box::new(source_requires),
            Box::new(Proposition::Implies(
                Box::new(source_ensures),
                Box::new(target_ensures),
            )),
        )),
    );
    Some(CFunctionContractRefinementObligations {
        entry,
        post,
        proposition,
    })
}

/// One forced pair of resource declarations: a target contract proof
/// parameter and the implementation binder that must stand for it. Both sides
/// read the same instance identity, so `root.model` on the named side and
/// `t.model` on the implementation side lower to the same term.
pub(super) struct RefinementInstanceBinding {
    target_identity: Variable,
    implementation_identity: Variable,
    entry: ResourceInstance,
    post: ResourceInstance,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum RefinementSide {
    Target,
    Implementation,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum RefinementPhase {
    Entry,
    Post,
}

/// One declared instance binder, with its family evaluated at the state that
/// declares it.
pub(super) struct DeclaredResourceInstance {
    identity: Variable,
    family: String,
    schema: ResourceFieldSchema,
    arguments: ResourceArguments,
}

/// Collects the instance binders a declaration names, in declaration order,
/// once per identity. `owns` states the same binder in `requires` and
/// `ensures`; the pair is one binder, not two.
pub(super) fn evaluate_declared_resource_instances(
    specs: &[&[CResourceSpec]],
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<DeclaredResourceInstance>>> {
    let mut seen = BTreeSet::new();
    let mut declared = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        if !spec.resource_arguments().is_empty() {
            return Ok(None);
        }
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if !seen.insert(identity) {
            continue;
        }
        let Some(schema) = spec.instance_schema() else {
            continue;
        };
        let Some(resource) = spec.instance_resource_spec() else {
            continue;
        };
        let instance = match evaluate_function_resource_spec(state, &resource, assumptions, budget)?
        {
            Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                DeclaredResourceInstance {
                    identity,
                    family: name,
                    schema: schema.clone(),
                    arguments,
                }
            }
            Ok(_) | Err(_) => return Ok(None),
        };
        declared.push(instance);
    }
    Ok(Some(declared))
}

/// Indexes declared binders by resource family. A family that appears twice
/// on one side leaves the binding unforced, so its entry is poisoned rather
/// than ranked.
pub(super) fn index_declared_instances_by_family(
    declared: &[DeclaredResourceInstance],
) -> Option<BTreeMap<&str, &DeclaredResourceInstance>> {
    let mut index = BTreeMap::new();
    for instance in declared {
        if index.insert(instance.family.as_str(), instance).is_some() {
            return None;
        }
    }
    Some(index)
}

/// Pairs the target contract's proof parameters with the implementation's
/// binders when exactly one pairing is possible, and instantiates one shared
/// instance per pair.
///
/// The pairing is a map lookup per binder: each side is indexed by resource
/// family once, a repeated family on either side refuses, and the two indexes
/// must have the same keys. No candidate is searched, scored, or preferred.
///
/// Each pair gets one entry instance with arbitrary fields, shared by both
/// entry states, and one post instance with fresh arbitrary fields, shared by
/// both post states. Fresh post fields are the same rule an ordinary call
/// applies to returned ownership: the identity survives, the field values do
/// not, and only the implementation's guarantees relate the two.
pub(super) fn forced_refinement_instance_bindings(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<RefinementInstanceBinding>>> {
    let Some(target) = evaluate_declared_resource_instances(
        &[contract.proof_parameters()],
        contract_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(implementation) = evaluate_declared_resource_instances(
        &[function.resource_requires(), function.resource_ensures()],
        function_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    if target.is_empty() && implementation.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let (Some(target_index), Some(implementation_index)) = (
        index_declared_instances_by_family(&target),
        index_declared_instances_by_family(&implementation),
    ) else {
        return Ok(None);
    };
    if target_index.len() != implementation_index.len() {
        return Ok(None);
    }
    let mut bindings = Vec::with_capacity(target_index.len());
    for (family, target) in &target_index {
        let Some(implementation) = implementation_index.get(family) else {
            return Ok(None);
        };
        if target.schema != implementation.schema
            || target.arguments.len() != implementation.arguments.len()
            || !target
                .arguments
                .iter()
                .zip(implementation.arguments.iter())
                .all(|(left, right)| {
                    crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                })
        {
            return Ok(None);
        }
        let identity = budget.allocate_kernel_variable()?;
        let instance = |budget: &mut ExecutionBudget| -> ExecutionResult<ResourceInstance> {
            let fields = arbitrary_resource_instance_fields(
                &target.schema,
                ModelFieldMintSite {
                    identity,
                    minted_by: &ModelMint::Refinement,
                },
                budget,
            )?;
            Ok(ResourceInstance::new(
                identity,
                target.family.clone(),
                target.arguments.clone(),
                target.schema.clone(),
                fields,
            )
            .expect("arbitrary fields have their declared types"))
        };
        bindings.push(RefinementInstanceBinding {
            target_identity: target.identity,
            implementation_identity: implementation.identity,
            entry: instance(budget)?,
            post: instance(budget)?,
        });
    }
    Ok(Some(bindings))
}

/// An arbitrary model field of `field_type` named by `variable`.
pub(in crate::kernel) fn resource_instance_field_value(
    field_type: &ResourceFieldType,
    variable: Variable,
) -> AlgebraicValue {
    match field_type {
        ResourceFieldType::Integer => AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
        ResourceFieldType::C(c_type) => AlgebraicValue::C(symbolic_call_result(*c_type, variable)),
        ResourceFieldType::Algebraic(algebraic_type) => AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }),
    }
}

/// Which instance's model is being replaced, and why. Carried to the two
/// field-minting funnels below so each fresh variable is registered as what it
/// is: a refusal that meets one later has no other way to find out
/// (`crate::kernel::model_fields`).
pub(in crate::kernel) struct ModelFieldMintSite<'a> {
    pub(in crate::kernel) identity: Variable,
    pub(in crate::kernel) minted_by: &'a ModelMint,
}

/// Registers the fields just minted for one instance. One insert per field,
/// beside the allocation that produced it, so this is bounded by the schema the
/// mint already walked.
pub(super) fn register_minted_model_fields(
    schema: &ResourceFieldSchema,
    site: &ModelFieldMintSite<'_>,
    fields: &[AlgebraicValue],
) {
    for (field_index, ((name, _), value)) in schema.fields().iter().zip(fields).enumerate() {
        let Some(variable) = algebraic_value_variable(value) else {
            continue;
        };
        crate::kernel::model_fields::register_model_field_variable(
            variable,
            ModelFieldOrigin {
                identity: site.identity,
                field: std::sync::Arc::from(name.as_str()),
                field_index,
                minted_by: site.minted_by.clone(),
            },
        );
    }
}

/// An arbitrary model for one instance, drawn through `variables` so the
/// fields avoid everything that stream reserves as well as everything else
/// the budget has issued.
pub(in crate::kernel) fn fresh_resource_instance_fields(
    schema: &ResourceFieldSchema,
    site: ModelFieldMintSite<'_>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceArguments> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            variables.next_in(budget)?,
        ));
    }
    register_minted_model_fields(schema, &site, &fields);
    Ok(fields.into_iter().collect())
}

/// The arbitrary model a join gives one named interface instance, drawn from
/// the join's own fresh-variable counter. Returns the fields and the counter
/// after them. It depends on nothing but its arguments, so the proof side
/// and the kernel's check of the join arrive at the same fields.
pub(crate) fn interface_join_instance_fields(
    schema: &ResourceFieldSchema,
    identity: Variable,
    next_kernel_variable: u64,
) -> Option<(ResourceArguments, u64)> {
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let fields = arbitrary_resource_instance_fields(
        schema,
        ModelFieldMintSite {
            identity,
            minted_by: &ModelMint::Join,
        },
        &mut budget,
    )
    .ok()?;
    Some((fields, budget.next_kernel_variable()))
}

pub(in crate::kernel) fn arbitrary_resource_instance_fields(
    schema: &ResourceFieldSchema,
    site: ModelFieldMintSite<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceArguments> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            budget.allocate_kernel_variable()?,
        ));
    }
    register_minted_model_fields(schema, &site, &fields);
    Ok(fields.into_iter().collect())
}

/// Installs the shared instances one side reads, under the identities that
/// side's declaration wrote.
pub(super) fn state_with_refinement_instances(
    state: &CState,
    bindings: &[RefinementInstanceBinding],
    side: RefinementSide,
    phase: RefinementPhase,
    assumptions: &PureFactContext,
) -> Option<CState> {
    if bindings.is_empty() {
        return Some(state.clone());
    }
    let mut state = state.clone();
    let mut names = BTreeMap::new();
    let mut facts = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let declared = match side {
            RefinementSide::Target => binding.target_identity,
            RefinementSide::Implementation => binding.implementation_identity,
        };
        let instance = match phase {
            RefinementPhase::Entry => &binding.entry,
            RefinementPhase::Post => &binding.post,
        };
        names.insert(declared, instance.identity());
        facts.push(CResourceFact::own(CResource::Instance(instance.clone())));
    }
    state.resource_bindings = Some(std::sync::Arc::new(names));
    state.resources = state
        .resources
        .clone()
        .try_compose_into_valid_context_delaying_normalization(facts, assumptions)
        .ok()?;
    Some(state)
}

pub(super) fn function_refines_named_contract_in_case(
    context: &CFunctionContractRefinementContext,
    case_assumptions: &[Proposition],
    unfolded_predicates: &BTreeSet<String>,
    explicit_case: bool,
    caller_facts: Option<&PureFactContext>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let contract = &context.contract;
    let function_interface = &context.function_interface;
    let contract_interface = contract.interface();
    if !predicate_interfaces_are_explicitly_compatible(
        contract_interface,
        function_interface,
        unfolded_predicates,
    ) {
        return Ok(false);
    }
    let mut propositions = contract_interface
        .contract_requires()
        .iter()
        .chain(contract_interface.contract_ensures())
        .chain(function_interface.contract_requires())
        .chain(function_interface.contract_ensures());
    let state_independent = propositions
        .clone()
        .all(spec_proposition_is_state_independent);
    let supported_syntax = propositions.all(spec_proposition_supports_stateful_memory_refinement);
    let supported_stateful_memory = !state_independent
        && !contract_interface.resource_requires().is_empty()
        && !contract_interface.resource_ensures().is_empty()
        && (!contract_interface.contract_mutable().is_empty()
            || contract_interface.resource_derived_mutable_frame())
        && supported_syntax;
    if !state_independent && !supported_stateful_memory {
        return Ok(false);
    }

    let contract_frame = function_contract_refinement_entry_state(context);
    let function_frame = function_contract_refinement_implementation_state(context);
    // Resource arguments are written over the two parameter lists, which the
    // views above already bind, so the pairing is decided before either
    // contract's own requirements are assumed.
    let Some(instances) = forced_refinement_instance_bindings(
        contract_interface,
        function_interface,
        &contract_frame,
        &function_frame,
        &PureFactContext::new(),
        budget,
    )?
    else {
        return Ok(false);
    };
    let install = |state: &CState, side, phase| {
        state_with_refinement_instances(state, &instances, side, phase, &PureFactContext::new())
    };
    let (Some(contract_entry), Some(function_entry)) = (
        install(
            &contract_frame,
            RefinementSide::Target,
            RefinementPhase::Entry,
        ),
        install(
            &function_frame,
            RefinementSide::Implementation,
            RefinementPhase::Entry,
        ),
    ) else {
        return Ok(false);
    };
    // Value arguments fixed by facts are the caller's terms, and a pure
    // contract reads nothing else of the caller, so the caller's facts about
    // those terms hold here. A contract over memory would read the frames'
    // own memories, which those facts do not describe.
    let mut preconditions = match caller_facts {
        Some(facts) if state_independent => facts.clone(),
        _ => PureFactContext::new(),
    };
    if !assume_contract_propositions(
        &contract_entry,
        &contract_entry,
        contract_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }
    preconditions = assumptions_with_propositions(&preconditions, case_assumptions);
    if !prove_contract_propositions(
        &function_entry,
        &function_entry,
        function_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }

    let post_memory = if state_independent {
        contract_entry.memory().clone()
    } else {
        let memory_variable = budget.allocate_kernel_variable()?;
        let mutable_ranges = if explicit_case {
            let Some(ranges) = evaluate_decided_contract_mutable_ranges_for_interface(
                function_interface,
                &function_entry,
                &preconditions,
                budget,
            )?
            else {
                return Ok(false);
            };
            ranges
        } else {
            let Some(ranges) = evaluate_contract_mutable_ranges_for_interface(
                contract_interface,
                &contract_entry,
                &preconditions,
                budget,
                true,
            )?
            else {
                return Ok(false);
            };
            ranges
        };
        contract_entry.memory().clone().with_call_memory_havoc(
            memory_variable,
            &mutable_ranges,
            &preconditions,
            None,
        )
    };
    let result = symbolic_contract_result(function_interface, context.result_variable);
    // The post states carry the post instances, so a guarantee written over
    // `t.model` reads the fields the call produced while `old(t.model)` still
    // reads the entry fields through the entry state passed alongside.
    let (Some(mut contract_post), Some(mut function_post)) = (
        install(
            &contract_frame.clone().with_memory(post_memory.clone()),
            RefinementSide::Target,
            RefinementPhase::Post,
        ),
        install(
            &function_frame.clone().with_memory(post_memory),
            RefinementSide::Implementation,
            RefinementPhase::Post,
        ),
    ) else {
        return Ok(false);
    };
    if function_interface.return_type() != CType::Void {
        set_contract_result(&mut contract_post, contract_interface, result.clone());
        set_contract_result(&mut function_post, function_interface, result);
    }
    let access_adapter = checked_access_mode_refinement_adapter(
        contract_interface,
        function_interface,
        &contract_entry,
        &function_entry,
        &function_post,
        &preconditions,
        budget,
    )?;
    if access_adapter == Some(false) {
        return Ok(false);
    }
    let resource_and_effects_compatible = if access_adapter == Some(true) {
        // The checked adapter has already established the resource transition
        // and recovery.  Keep the ordinary effect containment check, but do
        // not re-run the algebraic resource comparison that cannot represent
        // the temporary owner-to-view loan scope.
        mutable_footprint_is_compatible_for_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &preconditions,
            budget,
        )?
    } else {
        compatible_resource_and_effect_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &contract_post,
            &function_post,
            &preconditions,
            budget,
        )?
    };
    if !resource_and_effects_compatible {
        return Ok(false);
    }
    // A throw leaves memory as it was, since a throwing interface has no
    // effects, and binds the payload in both frames; the implementation's
    // exceptional guarantees must give the contract's. One that never throws
    // owes nothing here.
    let exceptional_preconditions =
        (!function_interface.exceptional_signature().is_empty()).then(|| preconditions.clone());
    let mut postconditions = preconditions;
    if !assume_contract_propositions(
        &function_post,
        &function_entry,
        function_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    if !prove_contract_propositions(
        &contract_post,
        &contract_entry,
        contract_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    let Some(mut exceptional) = exceptional_preconditions else {
        return Ok(true);
    };
    let payload = symbolic_call_result(CType::Int32, budget.allocate_kernel_variable()?);
    let throw_frame = |entry: &CState| {
        let mut state = entry.clone();
        state.locals.set_typed(
            C_EXCEPTIONAL_RESULT_NAME.to_string(),
            payload.clone(),
            CType::Int32,
        );
        state
    };
    let function_throw = throw_frame(&function_entry);
    let contract_throw = throw_frame(&contract_entry);
    if !assume_contract_propositions(
        &function_throw,
        &function_entry,
        function_interface.exceptional_ensures(),
        &mut exceptional,
        budget,
    )? {
        return Ok(false);
    }
    prove_contract_propositions(
        &contract_throw,
        &contract_entry,
        contract_interface.exceptional_ensures(),
        &mut exceptional,
        budget,
    )
}

/// Predicate bodies are stored as checked, normalized contract propositions,
/// while `predicate_unfoldings` retains their opaque surface identities. Equal
/// unfolding tables need no proof action. Every entry present on only one side
/// must otherwise have its predicate name explicitly opened by the proof.
pub(super) fn predicate_interfaces_are_explicitly_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    unfolded_predicates: &BTreeSet<String>,
) -> bool {
    let contract_unfoldings = contract
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let function_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let permitted = |unfolding: &CPredicateUnfolding| match unfolding.predicate() {
        SpecProposition::Predicate { name, .. } => unfolded_predicates.contains(name),
        _ => false,
    };
    contract_unfoldings
        .difference(&function_unfoldings)
        .chain(function_unfoldings.difference(&contract_unfoldings))
        .all(|unfolding| permitted(unfolding))
}
