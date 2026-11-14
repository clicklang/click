use super::*;

fn function(constant: bool) -> ProgramFunction {
    ProgramFunction::new(
        ProgramType::UInt8Pointer,
        "text",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_return_pointee_constant(constant)
}

fn pointer(constant: bool) -> ProgramValue {
    ProgramValue::typed_pointer(Pointer::symbolic(Variable(910)), ProgramType::UInt8Pointer)
        .with_pointer_pointee_constant(constant)
}

#[test]
fn pointee_const_return_coercion_enforces_declared_qualifier() {
    for source_const in [false, true] {
        for return_const in [false, true] {
            let result = coerce_function_return_value(
                pointer(source_const),
                &function(return_const),
                &mut Vec::new(),
                &PureFactContext::new(),
            );
            assert_eq!(result.is_some(), !source_const || return_const);
            if let Some(ProgramValue::Pointer(pointer)) = result {
                assert_eq!(pointer.pointee_constant(), return_const);
            }
        }
    }
}

#[test]
fn pointee_const_return_symbolic_result_and_binding_preserve_qualifier() {
    let function = function(true);
    let value = symbolic_function_result(&function, Variable(911));
    assert!(matches!(&value, ProgramValue::Pointer(pointer) if pointer.pointee_constant()));
    let parameter = int32(7);
    let mut state = ExecutionState::new().with_local("result", parameter.clone());
    set_function_result(&mut state, &function, value);
    assert_eq!(
        state.locals().get_native("result").as_deref(),
        Some(&parameter)
    );
    assert!(
        matches!(state.locals.binding(C_CONTRACT_RESULT_NAME), Some(LocalBinding::Object {
            value, pointee_constant: true, ..
        }) if value.pointer().is_some_and(|pointer| pointer.pointee_constant()))
    );
}

#[test]
fn pointee_const_return_contract_signature_checks_qualifier() {
    let mutable = function(false);
    assert!(!mutable.return_pointee_is_constant());
    let constant = function(true);
    let contract = FunctionContract::new("text_contract", constant.clone()).unwrap();
    assert!(contract.exactly_matches(&constant));
    assert!(contract.has_compatible_signature_and_resource_vocabulary(&constant));
    assert!(!contract.exactly_matches(&mutable));
    assert!(!contract.has_compatible_signature_and_resource_vocabulary(&mutable));
}

#[test]
fn pointee_const_return_function_address_cannot_convert_to_mutable_callback() {
    let target = function(true);
    let parameter = program_parameter("callback", function(false).function_pointer_type());
    let environment = ExecutionEnvironment::new().with_function(target);
    let value = type_function_address_value(
        &ProgramExpression::FunctionAddress("text".to_string()),
        ProgramValue::typed_pointer(
            Pointer {
                block: PointerBlock::Function("text".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ),
        Some(&environment),
    );
    assert!(coerce_program_function_argument_without_obligations(&value, &parameter).is_none());
}

#[test]
fn pointee_const_return_arguments_cannot_discard_const() {
    for constant in [false, true] {
        let parameter =
            program_parameter("text", ProgramType::UInt8Pointer).with_pointee_constant(constant);
        assert_eq!(
            coerce_program_function_argument_without_obligations(&pointer(true), &parameter)
                .is_some(),
            constant
        );
        let callee = ProgramFunction::new(
            ProgramType::Void,
            "consume",
            vec![parameter],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        assert_eq!(
            coerce_program_function_arguments(
                &callee,
                &[pointer(true)],
                &[],
                &PureFactContext::new()
            )
            .is_some(),
            constant
        );
    }
}

#[test]
fn pointee_const_return_string_literal_storage_is_read_only_but_type_is_mutable() {
    let function = ProgramFunction::new(
        ProgramType::UInt8Pointer,
        "literal_source",
        Vec::new(),
        program_return(crate::kernel::program_expression::variable("literal")),
    )
    .with_string_literals(vec![StringLiteral::new("literal", b"ok\0".to_vec())]);
    let state = initialize_program_function_globals(&ExecutionState::new(), &function);
    let paths = evaluate_program_expression_paths(
        &state,
        &crate::kernel::program_expression::variable("literal"),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("literal must evaluate")
    };
    assert!(
        matches!(value, ProgramValue::Pointer(pointer) if !pointer.pointee_constant()
            && state.memory.is_read_only_block(&pointer.block))
    );
    assert!(
        coerce_function_return_value(
            value.clone(),
            &function,
            &mut Vec::new(),
            &PureFactContext::new()
        )
        .is_some()
    );
}
