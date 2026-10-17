//! A call's arguments and result: evaluating and binding arguments, coercing argument and return values to the declared types, and symbolic results for calls whose body is not executed.

use super::*;

pub(super) fn with_contract_argument_views(
    state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> CState {
    with_contract_interface_argument_views(state, function.contract_interface(), values)
}

pub(super) fn with_contract_interface_argument_views(
    state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
) -> CState {
    let mut state = state.clone();
    state.resources = state.resources.unpublished_contract_view();
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            // Aggregate parameters are already represented by the copied
            // address-backed object installed by argument binding. Keeping
            // that binding lets contract field accesses inspect the copy
            // rather than accidentally replacing it with the caller's source
            // pointer.
            continue;
        }
        // Keep the contract view identical to the typed parameter binding.
        // In particular, a C null-pointer constant arrives here as the
        // caller's int32 `0`, but the callee parameter is a pointer.  Using
        // the raw caller value would overwrite the correctly coerced binding
        // and make pointer preconditions impossible to lower.
        let value = coerce_c_contract_argument_without_obligations(value, parameter)
            .expect("function arguments were type-checked before building contract views");
        let value = value
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
        if let CValue::Pointer(pointer) = &value {
            let Some(element_width) = parameter.c_type().pointee_type().map(CType::byte_width)
            else {
                // An opaque object pointer carries identity and qualifiers,
                // but no element width. Do not manufacture a contract view
                // that would make an untyped dereference look loadable.
                continue;
            };
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::view_memory(
                    CMemoryRange::new_with_element_width(
                        pointer.pointer().clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(i32::MAX as u32),
                        element_width,
                    ),
                ));
        }
    }
    state
}

pub(super) fn set_function_result(state: &mut CState, function: &CFunction, value: CValue) {
    set_contract_result(state, function.contract_interface(), value);
}

pub(super) fn set_contract_result(
    state: &mut CState,
    interface: &CFunctionContractInterface,
    value: CValue,
) {
    if let Some(layout) = interface.return_aggregate_layout()
        && let CValue::Pointer(pointer) = &value
    {
        if interface.aggregate_return_mode() == CAggregateReturnMode::Copy {
            state.set_memory(
                // A returned-by-value temporary is fresh caller storage. Its
                // declaration must remain in the memory history so copying
                // its fields does not disconnect unrelated input snapshots.
                // A symbolic pointer still supplies only a synthetic layout.
                if matches!(pointer.block, PointerBlock::Symbolic(_)) {
                    state
                        .memory
                        .clone()
                        .with_block_without_derivation(pointer.block.clone(), layout.size_bytes())
                } else {
                    state
                        .memory
                        .clone()
                        .with_block(pointer.block.clone(), layout.size_bytes())
                },
            );
        }
        state.locals.set_aggregate_object_at(
            C_CONTRACT_RESULT_NAME.to_string(),
            layout.clone(),
            pointer.pointer().clone(),
        );
        return;
    }
    state.locals.set_typed_with_all_qualifiers(
        C_CONTRACT_RESULT_NAME.to_string(),
        value
            .with_pointer_pointee_constant(interface.return_pointee_is_constant())
            .with_pointer_object_class(interface.return_pointee_class()),
        interface.return_type(),
        false,
        false,
        false,
        interface.return_pointee_is_constant(),
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AggregateReturnRefusal {
    InvalidValue,
    UninitializedRead,
}

// Keep initialization and result identity in one checked transition: copy mode
// materializes a value, while construction mode completes the selected object.
// Every body-completion path must use this boundary before retiring the source.
pub(super) fn complete_aggregate_return(
    state: &mut CState,
    function: &CFunction,
    value: CValue,
) -> Result<CValue, AggregateReturnRefusal> {
    if function.contract_interface().aggregate_return_mode() == CAggregateReturnMode::Construction {
        return construction_return::complete(state, function.contract_interface(), value);
    }
    let layout = function
        .return_aggregate_layout()
        .ok_or(AggregateReturnRefusal::InvalidValue)?;
    let CValue::Pointer(pointer) = value else {
        return Err(AggregateReturnRefusal::InvalidValue);
    };
    if pointer.is_null() {
        return Err(AggregateReturnRefusal::InvalidValue);
    }
    let source = pointer.pointer().clone();
    if aggregate_copy_reads_uninitialized(&state.memory, &source, layout) {
        return Err(AggregateReturnRefusal::UninitializedRead);
    }
    let frame = state.next_local_frame;
    let destination = CMemory::frame_local_pointer(frame, "__return");
    state.set_memory(
        state
            .memory
            .clone()
            .with_block(destination.block.clone(), layout.size_bytes()),
    );
    state.set_memory(copy_aggregate_fields(
        state.memory.clone(),
        &source,
        &destination,
        layout,
    ));
    state.next_local_frame = frame.saturating_add(1);
    Ok(CValue::typed_pointer(destination, function.return_type()))
}

/// The undefined behavior of the implicit conversion a `return` performs when
/// it converts a pointer into a freed allocation to a non-pointer return type
/// such as `_Bool`; see [`freed_pointer_use`]. Returning the pointer from a
/// pointer-returning function only moves it and is not refused. `state` is the
/// state at the `return`.
pub(super) fn freed_pointer_return_conversion(
    state: &CState,
    function: &CFunction,
    value: &CValue,
    assumptions: &PureFactContext,
) -> Option<CUndefinedBehavior> {
    let return_type = function.return_type();
    if return_type == CType::Void
        || return_type.is_pointer()
        || function.return_aggregate_layout().is_some()
        || state.memory().heap_has_no_deallocations()
    {
        return None;
    }
    freed_pointer_use(state, value, assumptions)
}

/// The undefined behavior of the implicit conversion a call performs when it
/// passes a pointer into a freed allocation to a non-pointer parameter such as
/// `_Bool`; see [`freed_pointer_use`]. Passing the pointer to a pointer
/// parameter only moves it and is not refused. `state` is the caller state the
/// arguments were evaluated in.
pub(super) fn freed_pointer_argument_conversion(
    state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
    assumptions: &PureFactContext,
) -> Option<CUndefinedBehavior> {
    if state.memory().heap_has_no_deallocations() {
        return None;
    }
    interface
        .parameters()
        .iter()
        .zip(values)
        .filter(|(parameter, _)| {
            parameter.aggregate_layout().is_none() && !parameter.c_type().is_pointer()
        })
        .find_map(|(_, value)| freed_pointer_use(state, value, assumptions))
}

/// The refusal of a call that passes a pointer to an object whose known
/// type the parameter's pointee type cannot designate
/// (`design/effective-types.md`). The callee is verified accessing the
/// object through that type, so the caller must not hand it another.
pub(super) fn incompatible_pointer_argument(
    state: &CState,
    function_name: &str,
    interface: &CFunctionContractInterface,
    values: &[CValue],
) -> Option<CRuntimeError> {
    interface
        .parameters()
        .iter()
        .zip(values)
        .find_map(|(parameter, value)| {
            let pointee = parameter.pointee_class()?;
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            let object = state
                .memory()
                .declared_class(pointer.pointer())
                .or_else(|| pointer.object_class())?;
            (!pointee.may_designate(&object)).then(|| {
                CRuntimeError::FunctionContract(format!(
                    "call to `{function_name}` passes an object of type `{}` to parameter \
                     `{}`, which points to `{}`: the callee accesses it through that type, \
                     and an object may be accessed only through its own type, up to \
                     signedness and qualifiers, or a character type (C11 6.5p7)",
                    object.spelling(),
                    parameter.name(),
                    pointee.spelling(),
                ))
            })
        })
}

/// The refusal of a return whose pointer designates an object of a known
/// type that the declared return type's pointee cannot designate; callers
/// access the object through that type (`design/effective-types.md`).
pub(super) fn incompatible_pointer_return(
    state: &CState,
    function: &CFunction,
    value: &CValue,
) -> Option<CRuntimeError> {
    let pointee = function.contract_interface().return_pointee_class()?;
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    let object = state
        .memory()
        .declared_class(pointer.pointer())
        .or_else(|| pointer.object_class())?;
    (!pointee.may_designate(&object)).then(|| {
        CRuntimeError::FunctionContract(format!(
            "`{}` returns a pointer to an object of type `{}` as a pointer to `{}`: its \
             callers access the object through that type, and an object may be accessed \
             only through its own type, up to signedness and qualifiers, or a character \
             type (C11 6.5p7)",
            function.name(),
            object.spelling(),
            pointee.spelling(),
        ))
    })
}

pub(super) fn coerce_function_return_value(
    value: CValue,
    function: &CFunction,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // Plain struct returns use `uint8*` as their internal ABI slot, while the
    // source expression that supplies the value retains the pointee type of
    // the object it addresses (for example, `int32*` for `return *source`).
    // The aggregate return materializer copies through the pointer and is the
    // type boundary that validates the complete object. The C0 struct model
    // uses `int32*` for a struct pointer and `uint8*` for an address-backed
    // struct value, so only those two data-pointer views cross this boundary.
    if function.return_aggregate_layout().is_some()
        && let CValue::Pointer(pointer) = &value
        && matches!(pointer.c_type(), CType::Int32Pointer | CType::UInt8Pointer)
        && !pointer.pointer().block.is_function()
    {
        return Some(CValue::typed_pointer(
            pointer.pointer().clone(),
            function.return_type(),
        ));
    }
    coerce_c_value_with_pointee_constant(
        value,
        function.return_type(),
        function.return_pointee_is_constant(),
        obligations,
        assumptions,
    )
}

pub(in crate::kernel) fn coerce_c_value_with_pointee_constant(
    value: CValue,
    c_type: CType,
    pointee_constant: bool,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // This is an implicit conversion boundary. Explicit C casts have their
    // own rules; storage read-only status is independently checked on writes.
    if matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant())
        && c_type.is_pointer()
        && !pointee_constant
    {
        return None;
    }
    Some(
        coerce_c_value_to_type(value, c_type, obligations, assumptions)?
            .with_pointer_pointee_constant(pointee_constant),
    )
}

#[cfg(test)]
pub(super) fn symbolic_function_result(function: &CFunction, variable: Variable) -> CValue {
    symbolic_contract_result(function.contract_interface(), variable)
}

pub(super) fn symbolic_contract_result(
    interface: &CFunctionContractInterface,
    variable: Variable,
) -> CValue {
    // An aggregate returned by value is not a pointer the callee handed over:
    // it is a fresh object the C abstract machine creates for the caller to
    // copy out of, and the program has no name and no prior pointer for it.
    // Giving it a `Temporary` identity rather than a symbolic one is what lets
    // `PointerBlock::proven_distinct` separate it from every other block, so a
    // read of one of its fields is framed across an unrelated store by
    // structure alone. A symbolic block would be separated from nothing, and a
    // load through it would then need aliasing evidence that no honest contract
    // about a returned struct can state.
    if interface.return_aggregate_layout().is_some() {
        return CValue::typed_pointer(
            Pointer::verifier_temporary(variable),
            interface.return_type(),
        )
        .with_pointer_pointee_constant(interface.return_pointee_is_constant());
    }
    symbolic_call_result(interface.return_type(), variable)
        .complete_word(Pointer::symbolic(variable))
        .with_pointer_pointee_constant(interface.return_pointee_is_constant())
        .with_pointer_object_class(interface.return_pointee_class())
}

pub(crate) fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::Bool => crate::kernel::bool_value(Bitvector32Term::Variable(variable)),
        CType::VoidPointer | CType::VoidPointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::Int8 => CValue::Int8(Bitvector32Term::Variable(variable)),
        CType::Int16 => CValue::Int16(Bitvector32Term::Variable(variable)),
        CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Variable(variable)),
        CType::UInt16 => CValue::UInt16(Bitvector32Term::Variable(variable)),
        CType::UInt32 => CValue::UInt32(Bitvector32Term::Variable(variable)),
        CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variable)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variable)),
        CType::Int128 => CValue::Int128(Bitvector32Term::Variable(variable)),
        CType::UInt128 => CValue::UInt128(Bitvector32Term::Variable(variable)),
        CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variable)),
        CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variable)),
        CType::Int8Pointer | CType::Int8PointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int128Pointer
        | CType::Int64Pointer
        | CType::UInt128Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int128PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt128PointerPointer
        | CType::UInt64PointerPointer
        | CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::FunctionPointer(_) => {
            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
        }
        CType::Int8Array(_) => {
            unreachable!("C functions cannot return array values")
        }
        CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int128Array(_)
        | CType::Int64Array(_)
        | CType::UInt128Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => {
            unreachable!("C functions cannot return array values")
        }
        CType::PointerArray(_, _) => {
            unreachable!("C functions cannot return array values")
        }
    }
}

pub(in crate::kernel) fn add_memory_store_obligation(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(pointer, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: value.byte_width(),
        },
    )?;
    Some(obligations)
}

pub(in crate::kernel) fn evaluate_c_arguments_paths(
    state: &CState,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    environment: Option<&CExecutionEnvironment>,
) -> ExecutionResult<Vec<CArgumentsPath>> {
    let mut paths = vec![CArgumentsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let argument_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for argument_path in
                evaluate_c_expression_paths(state, argument, &argument_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match argument_path.outcome {
                    CExpressionOutcome::Value(value) => {
                        let value = type_function_address_value(argument, value, environment);
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgumentsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        next_paths.push(CArgumentsPath {
                            values: path.values.clone(),
                            outcome: Some(CFunctionOutcome::UndefinedBehavior(undefined_behavior)),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => next_paths.push(CArgumentsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        budget.check_path_width(next_paths.len())?;
        paths = next_paths;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn type_function_address_value(
    expression: &CExpression,
    value: CValue,
    environment: Option<&CExecutionEnvironment>,
) -> CValue {
    let CExpression::FunctionAddress(name) = expression else {
        return value;
    };
    let Some(environment) = environment else {
        return value;
    };
    let Some(function) = environment.get_function(name) else {
        return value;
    };
    match value {
        CValue::Pointer(pointer)
            if pointer.block.is_function()
                && pointer.c_type() == CType::FunctionPointer(CallbackSignature::UNSPECIFIED) =>
        {
            // Return and parameter qualifications belong to the callback
            // signature, not to the function-pointer object's pointee view.
            CValue::typed_pointer(pointer.into_pointer(), function.function_pointer_type())
        }
        value => value,
    }
}

pub(super) fn argument_binding_error(function: &CFunction, values: &[CValue]) -> String {
    contract_argument_binding_error(function.contract_interface(), function.name(), values)
}

pub(super) fn contract_argument_binding_error(
    interface: &CFunctionContractInterface,
    name: &str,
    values: &[CValue],
) -> String {
    if interface
        .parameters()
        .iter()
        .zip(values)
        .any(|(parameter, value)| {
            matches!(
                (parameter.c_type(), value),
                (CType::FunctionPointer(expected), CValue::Pointer(actual))
                    if actual.block.is_function()
                        && actual.c_type() != CType::FunctionPointer(expected)
            )
        })
    {
        format!(
            "incompatible signature for function pointer argument to {}",
            name
        )
    } else {
        format!("could not bind arguments for {name}")
    }
}

/// A function-level path carries the loadability of its own string literals
/// across the call boundary. This is intentionally derived from the function
/// metadata rather than by scanning all read-only memory, so a call summary
/// cannot accidentally certify an unrelated block.
pub(super) fn append_string_literal_loadable_facts(
    function: &CFunction,
    outcome: &CFunctionOutcome,
    facts: &mut ExecutionFacts,
) {
    let state = match outcome {
        CFunctionOutcome::Return { state, .. } | CFunctionOutcome::Throw { state, .. } => state,
        _ => return,
    };
    for literal in function.string_literals() {
        let base =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        let proposition = Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base,
            bytes: Bitvector32Term::Constant(literal.bytes().len() as u32),
            wide: false,
        };
        if !facts.iter().any(|fact| fact.proposition() == &proposition) {
            facts.push(ExecutionPureFact::certified(proposition));
        }
    }
}

/// Collect the expressions that read memory when a function body is executed.
///
/// A verified call normally applies the function's contract without executing
/// its body. That is sound for external memory, whose initialization is part
/// of the caller's loadability authority, but a caller's automatic object has
/// a separate initialization history. Keeping the read expressions lets the
/// call boundary recheck that history without rerunning the body or treating a
/// resource transfer as an initialization event.
pub(super) fn collect_c_memory_read_expressions(
    statement: &CStatement,
    reads: &mut Vec<CExpression>,
) {
    fn values(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Subobject {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression) => values(expression, reads),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                values(condition, reads);
                values(then_branch, reads);
                values(else_branch, reads);
            }
            CExpression::AddressOf(target) | CExpression::CheckedObjectAddress(target) => {
                lvalue_address(target, reads)
            }
            CExpression::Load(pointer) => {
                reads.push(expression.clone());
                values(pointer, reads);
            }
            CExpression::TypedLoad {
                pointer,
                value_type,
                ..
            } => {
                if !matches!(
                    value_type,
                    CType::Int32Array(_)
                        | CType::UInt8Array(_)
                        | CType::Int8Array(_)
                        | CType::Int16Array(_)
                        | CType::UInt16Array(_)
                        | CType::UInt32Array(_)
                        | CType::Int128Array(_)
                        | CType::Int64Array(_)
                        | CType::UInt128Array(_)
                        | CType::UInt64Array(_)
                        | CType::Float32Array(_)
                        | CType::Float64Array(_)
                ) {
                    reads.push(expression.clone());
                }
                values(pointer, reads);
            }
            CExpression::Index(base, index) => {
                reads.push(expression.clone());
                values(base, reads);
                values(index, reads);
            }
            crate::kernel::binary_c_operation!(left, right) => {
                values(left, reads);
                values(right, reads);
            }
        }
    }

    fn lvalue_address(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Variable(_) => {}
            CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                values(pointer, reads)
            }
            CExpression::Index(base, index) => {
                values(base, reads);
                values(index, reads);
            }
            _ => values(expression, reads),
        }
    }

    match statement {
        CStatement::Skip
        | CStatement::EndScalarReference(_)
        | CStatement::ScalarReferenceScope(_)
        | CStatement::EndAutomaticLifetimes { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare {
            initializer: None, ..
        }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ForStep { step, .. } => collect_c_memory_read_expressions(step, reads),
        CStatement::CopyAggregate { target, source, .. }
        | CStatement::InitializeScalarArray { target, source, .. } => {
            lvalue_address(target, reads);
            values(source, reads);
        }
        CStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | CStatement::Assign { expression, .. } => values(expression, reads),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                values(argument, reads);
            }
        }
        CStatement::HeapAllocate { bytes, .. } => values(bytes, reads),
        CStatement::HeapFree { pointer } => values(pointer, reads),
        CStatement::Assert { condition, .. } => values(condition, reads),
        CStatement::Seq(first, second) => {
            collect_c_memory_read_expressions(first, reads);
            collect_c_memory_read_expressions(second, reads);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_c_memory_read_expressions(try_body, reads);
            collect_c_memory_read_expressions(handler, reads);
        }
        CStatement::Return(expression) | CStatement::Throw(expression) => values(expression, reads),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            lvalue_address(pointer, reads);
            values(value, reads);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            values(target, reads);
            values(operand, reads);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(then_branch, reads);
            collect_c_memory_read_expressions(else_branch, reads);
        }
        CStatement::While {
            condition, body, ..
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(body, reads);
        }
        CStatement::Switch { expression, cases } => {
            values(expression, reads);
            for case in cases {
                collect_c_memory_read_expressions(&case.body, reads);
            }
        }
    }
}

pub(super) fn c_expression_mentions_pointer_parameter(
    expression: &CExpression,
    pointer_parameters: &BTreeSet<String>,
) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Variable(name) => pointer_parameters.contains(name),
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::CheckedObjectAddress(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Subobject {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression) => {
            c_expression_mentions_pointer_parameter(expression, pointer_parameters)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_mentions_pointer_parameter(pointer, pointer_parameters)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_pointer_parameter(condition, pointer_parameters)
                || c_expression_mentions_pointer_parameter(then_branch, pointer_parameters)
                || c_expression_mentions_pointer_parameter(else_branch, pointer_parameters)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            c_expression_mentions_pointer_parameter(left, pointer_parameters)
                || c_expression_mentions_pointer_parameter(right, pointer_parameters)
        }
    }
}

pub(super) fn verified_call_uninitialized_read(
    entry_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    selected_load_values: &BTreeMap<(Pointer, CType), CValue>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CUndefinedBehavior>> {
    // Aggregate copies have their own field-by-field initialization checks at
    // execution time. Their lowered lvalues also include typed array views
    // that are not scalar reads of a transferred pointer parameter.
    if function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some())
    {
        return Ok(None);
    }
    let mut reads = Vec::new();
    collect_c_memory_read_expressions(function.body(), &mut reads);
    let pointer_parameters = function
        .parameters()
        .iter()
        .filter(|parameter| parameter.c_type().is_pointer())
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    for read in reads
        .into_iter()
        .filter(|read| c_expression_mentions_pointer_parameter(read, &pointer_parameters))
    {
        for path in evaluate_c_expression_paths(entry_state, &read, assumptions, budget)? {
            if let CExpressionOutcome::UndefinedBehavior(undefined_behavior) = path.outcome
                && undefined_behavior == CUndefinedBehavior::UninitializedRead
            {
                if let CExpression::TypedLoad {
                    pointer,
                    value_type,
                    volatile: false,
                    ..
                } = &read
                    && let Ok(CValue::Pointer(address)) = evaluate_loop_effect_segment_value(
                        entry_state,
                        pointer,
                        assumptions,
                        "selected call field address",
                        budget,
                    )?
                    && selected_load_values.contains_key(&(address.pointer().clone(), *value_type))
                {
                    continue;
                }
                return Ok(Some(undefined_behavior));
            }
        }
    }
    Ok(None)
}

pub(in crate::kernel) fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    // Preserve the value-only representation for parameters whose addresses
    // never escape. Besides avoiding unnecessary memory cells, this
    // keeps ordinary call summaries unchanged. A frame is needed only when
    // the function body actually contains an address-taking expression for a
    // parameter.
    let mut address_taken = BTreeSet::new();
    crate::kernel::loops::collect_address_taken_locals(function.body(), &mut address_taken);
    let address_taken_parameters = function
        .parameters()
        .iter()
        // Taking the address of a pointer parameter's pointee (for example
        // `&p[1]`) mentions `p` while addressing the pointed-to object, not the
        // parameter object itself. A volatile pointer parameter is different:
        // its own object is the access, so it needs an address-backed slot for
        // the volatile event to name.
        .filter(|parameter| {
            (address_taken.contains(parameter.name()) || parameter.is_volatile())
                && (parameter.is_volatile() && parameter.c_type().is_pointer()
                    || matches!(
                        parameter.c_type(),
                        CType::Int8
                            | CType::Int16
                            | CType::Int32
                            | CType::UInt8
                            | CType::UInt16
                            | CType::UInt32
                            | CType::Float32
                            | CType::Float64
                    ))
        })
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(
            if address_taken_parameters.is_empty() && !has_aggregate_parameters {
                frame
            } else {
                frame.saturating_add(1)
            },
        )
        .with_next_local_lifetime(caller_state.next_local_lifetime())
        // The body below declares its locals into the caller's memory with
        // this fresh locals map, which cannot see the caller's objects. Pass
        // down whether there are any to collide with, so each declaration
        // that could take a caller's `local:<name>` takes its own identity
        // instead. A frame that has bound nothing owns nothing, which is what
        // makes the outermost one answer no.
        .with_enclosing_frame_holds_locals(
            caller_state.enclosing_frame_holds_locals() || !caller_state.locals.is_empty(),
        );
    callee_state.mutex_ledger = caller_state.mutex_ledger.clone();
    callee_state.mutex_input_reservations = caller_state.mutex_input_reservations.clone();
    callee_state.opaque_mutex_acquisitions = caller_state.opaque_mutex_acquisitions.clone();
    callee_state.named_mutex_authorities = caller_state.named_mutex_authorities.clone();
    // The caller's outstanding workers stay outstanding across the call. A
    // callee cannot join them (each completion right names the caller's loan
    // participant), and returning its ledger must not erase their rights or
    // the population changes they defer to join.
    callee_state.thread_ledger = caller_state.thread_ledger.clone();
    callee_state.preserves_mutex_protocols = caller_state.preserves_mutex_protocols
        || preserves_mutex_protocols(function.contract_interface());
    callee_state.population_access = caller_state.population_access.clone();
    callee_state.observed_population_families = caller_state.observed_population_families.clone();
    Arc::make_mut(&mut callee_state.population_effects).creation = caller_state
        .population_effects
        .creation
        .as_ref()
        .map(|events| events.enter_call());
    // A function entry is a lexical/frame rebind, not an authority reset.
    // Preserve an already-active candidate loan through calls whose resource
    // interface is empty; the resource-transfer planner may replace these
    // fields with a checked callee participant when it lends new views.
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    callee_state = initialize_c_function_globals(&callee_state, function);
    for (parameter, value) in function.parameters().iter().zip(values) {
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            register_aggregate_argument_source(&slot.block, &source);
            // Preserve the caller's memory snapshot for symbolic source
            // loads. Declaring the destination first would make an unknown
            // external field load depend on the callee's fresh block and
            // prevent entry facts from relating it to the caller's value.
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot.clone(),
            );
            // A by-value parameter owns its fresh private bytes, just as an
            // aggregate local does. This grants no authority over pointers
            // stored inside it or over the caller's original object.
            callee_state.resources = callee_state
                .resources
                .clone()
                .unchecked_with_fact(private_aggregate_storage_owner(slot, layout));
            continue;
        }
        let value = coerce_c_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant())
            .with_pointer_object_class(parameter.pointee_class());
        if address_taken_parameters.contains(parameter.name()) {
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, parameter.c_type().abi_alignment());
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), value.byte_width())
                    .store(slot.clone(), value.clone()),
            );
            callee_state.locals.set_typed_qualified_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                slot,
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        } else {
            callee_state.locals.set_typed_qualified_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                CMemory::value_parameter_pointer(parameter.name()),
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        }
    }
    // A contract's value parameters, such as a binder's `s.len`, follow the
    // C arguments when a proof is entered: at fresh values, as the C
    // parameters are, so the proof holds for every value.
    let value_parameters = function.contract_interface().value_parameters();
    let c_count = function.parameters().len();
    if !value_parameters.is_empty() && values.len() == c_count + value_parameters.len() {
        super::super::api::bind_contract_value_parameters(
            &mut callee_state,
            value_parameters,
            &values[c_count..],
        );
    }
    construction_return::bind(
        caller_state,
        function.contract_interface(),
        &mut callee_state,
    )?;
    Some(callee_state)
}

/// Binds only the locals needed to instantiate a body-independent contract
/// interface. This intentionally does not inspect a statement body or collect
/// address-taken locals. A direct application can additionally supply its
/// concrete declaration identity so global and static names in the interface
/// resolve to the program's stable storage; that identity is not body-proof
/// evidence. Named callbacks supply no concrete storage.
pub(super) fn bind_c_contract_arguments(
    caller_state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
    storage: Option<&CFunction>,
) -> Option<CState> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = interface
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(if has_aggregate_parameters {
            frame.saturating_add(1)
        } else {
            frame
        })
        .with_next_local_lifetime(caller_state.next_local_lifetime())
        .with_enclosing_frame_holds_locals(
            caller_state.enclosing_frame_holds_locals() || !caller_state.locals.is_empty(),
        );
    callee_state.mutex_ledger = caller_state.mutex_ledger.clone();
    callee_state.mutex_input_reservations = caller_state.mutex_input_reservations.clone();
    callee_state.opaque_mutex_acquisitions = caller_state.opaque_mutex_acquisitions.clone();
    callee_state.named_mutex_authorities = caller_state.named_mutex_authorities.clone();
    // The caller's outstanding workers stay outstanding across the call. A
    // callee cannot join them (each completion right names the caller's loan
    // participant), and returning its ledger must not erase their rights or
    // the population changes they defer to join.
    callee_state.thread_ledger = caller_state.thread_ledger.clone();
    callee_state.preserves_mutex_protocols =
        caller_state.preserves_mutex_protocols || preserves_mutex_protocols(interface);
    callee_state.population_access = caller_state.population_access.clone();
    callee_state.observed_population_families = caller_state.observed_population_families.clone();
    Arc::make_mut(&mut callee_state.population_effects).creation = caller_state
        .population_effects
        .creation
        .as_ref()
        .map(|events| events.enter_call());
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    if let Some(function) = storage {
        callee_state = initialize_c_function_globals(&callee_state, function);
    }
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot,
            );
            continue;
        }
        let value = coerce_c_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant())
            .with_pointer_object_class(parameter.pointee_class());
        callee_state.locals.set_typed_qualified_with_all_qualifiers(
            parameter.name().to_string(),
            value,
            parameter.c_type(),
            CMemory::value_parameter_pointer(parameter.name()),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
    }
    construction_return::bind(caller_state, interface, &mut callee_state)?;
    Some(callee_state)
}

pub(super) fn coerce_c_function_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    coerce_c_contract_argument_without_obligations(value, parameter)
}

pub(super) fn coerce_c_contract_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    let mut obligations = Vec::new();
    let value = coerce_c_value_with_pointee_constant(
        value.clone(),
        parameter.c_type(),
        parameter.pointee_is_constant(),
        &mut obligations,
        &PureFactContext::new(),
    )?;
    obligations.is_empty().then_some(value)
}

pub(super) fn coerce_c_function_arguments(
    function: &CFunction,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    coerce_c_contract_arguments(
        function.contract_interface(),
        values,
        existing_obligations,
        assumptions,
    )
}

pub(super) fn coerce_c_contract_arguments(
    interface: &CFunctionContractInterface,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let mut obligations = existing_obligations.to_vec();
    let mut coerced = Vec::with_capacity(values.len());
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            coerced.push(value.clone());
        } else {
            // A contract stated over one integer type's cells accepts a
            // pointer to the other signedness of the same width: C11 6.5p7
            // lets either read the object, and loads read a cell of either
            // signedness through either type (`CType::read_cell`). This is
            // how a byte contract such as `strlen`'s serves a signed plain
            // `char *`.
            let value = match value {
                CValue::Pointer(pointer)
                    if parameter.c_type() != pointer.c_type()
                        && parameter.c_type().is_signedness_view_of(pointer.c_type()) =>
                {
                    CValue::Pointer(pointer.clone().with_type(parameter.c_type()))
                }
                value => value.clone(),
            };
            coerced.push(coerce_c_value_with_pointee_constant(
                value,
                parameter.c_type(),
                parameter.pointee_is_constant(),
                &mut obligations,
                assumptions,
            )?);
        }
    }
    Some((coerced, obligations))
}
