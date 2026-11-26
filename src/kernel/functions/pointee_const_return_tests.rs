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

#[test]
fn pointee_const_return_symbolic_result_and_binding_preserve_qualifier() {
    let function = function(true);
    let value = symbolic_function_result(&function, Variable(911));
    assert!(matches!(&value, ProgramValue::Pointer(_)));
    let parameter = int32(7);
    let mut state = ExecutionState::new().with_local("result", parameter.clone());
    set_function_result(&mut state, &function, value);
    assert_eq!(
        state.locals().get_native("result").as_deref(),
        Some(&parameter)
    );
    assert!(matches!(
        state.locals.binding(CONTRACT_RESULT),
        Some(LocalBinding::Object {
            pointee_constant: true,
            ..
        })
    ));
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
            OldAddress {
                base: AddressBase::Function("text".to_string()),
                offset: AddressOffset::constant(0),
            },
            ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ),
        Some(&environment),
    );
    assert!(coerce_program_function_argument_without_obligations(&value, &parameter).is_none());
}

#[test]
fn pointee_const_return_string_literal_storage_is_read_only_but_type_is_mutable() {
    let function = ProgramFunction::new(
        ProgramType::UInt8Pointer,
        "literal_source",
        Vec::new(),
        program_return(ProgramExpression::StringLiteral(StringLiteralId::new(
            "literal_source",
            0,
        ))),
    )
    .with_string_literals(vec![StringLiteral::new(
        StringLiteralId::new("literal_source", 0),
        b"ok\0".to_vec(),
    )]);
    let state = initialize_program_function_globals(&ExecutionState::new(), &function);
    let paths = evaluate_program_expression_paths(
        &state,
        &ProgramExpression::StringLiteral(StringLiteralId::new("literal_source", 0)),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("literal must evaluate")
    };
    assert!(matches!(value, ProgramValue::Pointer(pointer) if !false
            && state.memory.is_read_only_block(&pointer.base)));
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
