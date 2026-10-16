use super::*;

fn function(constant: bool) -> CFunction {
    CFunction::new(
        CType::UInt8Pointer,
        "text",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_return_pointee_constant(constant)
}

fn pointer(constant: bool) -> CValue {
    CValue::typed_pointer(Pointer::symbolic(Variable(910)), CType::UInt8Pointer)
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
            if let Some(CValue::Pointer(pointer)) = result {
                assert_eq!(pointer.pointee_constant(), return_const);
            }
        }
    }
}

#[test]
fn pointee_const_return_symbolic_result_and_binding_preserve_qualifier() {
    let function = function(true);
    let value = symbolic_function_result(&function, Variable(911));
    assert!(matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant()));
    let parameter = int32(7);
    let mut state = CState::new().with_local("result", parameter.clone());
    set_function_result(&mut state, &function, value);
    assert_eq!(state.locals().get("result"), Some(&parameter));
    assert!(
        matches!(state.locals.binding(C_CONTRACT_RESULT_NAME), Some(CLocalBinding::Object {
            value: CValue::Pointer(pointer), pointee_constant: true, ..
        }) if pointer.pointee_constant())
    );
}

#[test]
fn pointee_const_return_contract_signature_checks_qualifier() {
    let mutable = function(false);
    assert!(!mutable.return_pointee_is_constant());
    let constant = function(true);
    let contract = CFunctionContract::new("text_contract", constant.clone()).unwrap();
    assert!(contract.exactly_matches(&constant));
    assert!(contract.has_compatible_signature_and_resource_vocabulary(&constant));
    assert!(!contract.exactly_matches(&mutable));
    assert!(!contract.has_compatible_signature_and_resource_vocabulary(&mutable));
}

#[test]
fn pointee_const_return_function_address_cannot_convert_to_mutable_callback() {
    let target = function(true);
    let parameter = c_parameter("callback", function(false).function_pointer_type());
    let environment = CExecutionEnvironment::new().with_function(target);
    let value = type_function_address_value(
        &CExpression::FunctionAddress("text".to_string()),
        CValue::typed_pointer(
            Pointer {
                block: PointerBlock::Function("text".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
        ),
        Some(&environment),
    );
    assert!(coerce_c_function_argument_without_obligations(&value, &parameter).is_none());
}

#[test]
fn pointee_const_return_arguments_cannot_discard_const() {
    for constant in [false, true] {
        let parameter = c_parameter("text", CType::UInt8Pointer).with_pointee_constant(constant);
        assert_eq!(
            coerce_c_function_argument_without_obligations(&pointer(true), &parameter).is_some(),
            constant
        );
        let callee = CFunction::new(
            CType::Void,
            "consume",
            vec![parameter],
            c_return(c_int32_literal(0)),
        );
        assert_eq!(
            coerce_c_function_arguments(&callee, &[pointer(true)], &[], &PureFactContext::new())
                .is_some(),
            constant
        );
    }
}

#[test]
fn pointee_const_return_string_literal_storage_is_read_only_but_type_is_mutable() {
    let function = CFunction::new(
        CType::UInt8Pointer,
        "literal_source",
        Vec::new(),
        c_return(c_variable("literal")),
    )
    .with_string_literals(vec![CStringLiteral::new("literal", b"ok\0".to_vec())]);
    let state = initialize_c_function_globals(&CState::new(), &function);
    let paths = evaluate_c_expression_paths(
        &state,
        &c_variable("literal"),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let CExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("literal must evaluate")
    };
    assert!(
        matches!(value, CValue::Pointer(pointer) if !pointer.pointee_constant()
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
