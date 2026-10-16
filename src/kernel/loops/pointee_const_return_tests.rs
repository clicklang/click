use super::*;
// Surface planning; only this test reaches it from inside the kernel.
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn pointee_const_return_rebinding_is_allowed_but_store_through_pointer_is_not() {
    let value = CValue::typed_pointer(Pointer::symbolic(Variable(916)), CType::Int32Pointer);
    let mut state = CState::new().with_local("p", value.clone());
    state.locals.set_typed_with_all_qualifiers(
        "q",
        value,
        CType::Int32Pointer,
        false,
        false,
        false,
        true,
    );
    let environment = CExecutionEnvironment::new();
    let paths = execute_c_statement_paths(
        &state,
        &c_assign("q", c_variable("p")),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let CStatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("const pointee does not prohibit rebinding")
    };
    assert!(matches!(
        state.locals.binding("q"),
        Some(CLocalBinding::Object {
            pointee_constant: true,
            ..
        })
    ));
    let paths = execute_c_statement_paths(
        state,
        &c_store(c_variable("q"), c_int32_literal(1)),
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn pointee_const_return_inline_call_preserves_pointer_identity() {
    let function = CFunction::new(
        CType::Int32Pointer,
        "view",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_variable("p")),
    )
    .with_return_pointee_constant(true)
    .with_inline_body();
    let value = CValue::typed_pointer(Pointer::symbolic(Variable(917)), CType::Int32Pointer);
    let state = CState::new().with_local("p", value.clone());
    let environment = CExecutionEnvironment::new().with_function(function);
    let paths = execute_c_call_assign_paths(
        &state,
        "temporary",
        "view",
        &[c_variable("p")],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let CStatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("inline call must return")
    };
    let result = state.locals.get("temporary").unwrap();
    assert!(matches!(result, CValue::Pointer(pointer) if pointer.pointee_constant()));
    let equality =
        c_value_comparison_proposition(result, CComparisonOperator::Equal, &value).unwrap();
    assert!(PureFactContext::new().proves(&equality));
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn pointee_const_return_direct_and_callback_calls_preserve_const() {
    let function = CFunction::new(
        CType::UInt8Pointer,
        "text",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_return_pointee_constant(true);
    let function_type = function.function_pointer_type();
    let environment = CExecutionEnvironment::new().with_function(function);
    let paths = execute_c_call_assign_paths(
        &CState::new(),
        "temporary",
        "text",
        &[],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { pointee_constant: true, .. }))));
    let state = CState::new().with_local(
        "callback",
        CValue::typed_pointer(
            Pointer {
                block: PointerBlock::Function("text".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            function_type,
        ),
    );
    let paths = execute_c_call_assign_paths(
        &state,
        "temporary",
        "callback",
        &[],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { pointee_constant: true, .. }))));

    let state = state.with_local(
        "mutable",
        CValue::typed_pointer(Pointer::null(), CType::UInt8Pointer),
    );
    let paths = execute_c_call_assign_paths(
        &state,
        "mutable",
        "callback",
        &[],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    ));

    let incompatible =
        CType::FunctionPointer(CType::function_pointer_signature(CType::UInt8Pointer, &[]));
    let state = CState::new().with_local(
        "callback",
        CValue::typed_pointer(
            Pointer {
                block: PointerBlock::Function("text".into()),
                offset: PointerOffsetTerm::Constant(0),
            },
            incompatible,
        ),
    );
    let paths = execute_c_call_assign_paths(
        &state,
        "temporary",
        "callback",
        &[],
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(_))
    ));
}

#[test]
fn pointee_const_return_assignment_preserves_destination_and_temporary_qualifiers() {
    for source_const in [false, true] {
        for destination_const in [false, true] {
            for immutable in [false, true] {
                let value =
                    CValue::typed_pointer(Pointer::symbolic(Variable(912)), CType::UInt8Pointer)
                        .with_pointer_pointee_constant(source_const);
                let mut state = CState::new();
                state.locals.set_typed_with_all_qualifiers(
                    "text",
                    value.clone(),
                    CType::UInt8Pointer,
                    false,
                    false,
                    immutable,
                    destination_const,
                );
                let result = assign_call_result(
                    &mut state,
                    "text",
                    value,
                    &mut Vec::new(),
                    &PureFactContext::new(),
                );
                assert_eq!(
                    result.is_ok(),
                    !immutable && (!source_const || destination_const)
                );
                if result.is_ok() {
                    assert!(
                        matches!(state.locals.binding("text"), Some(CLocalBinding::Object { value: CValue::Pointer(pointer), pointee_constant, .. })
                            if *pointee_constant == destination_const && pointer.pointee_constant() == destination_const)
                    );
                }
            }
        }
    }
    let value = CValue::typed_pointer(Pointer::symbolic(Variable(913)), CType::UInt8Pointer)
        .with_pointer_pointee_constant(true);
    let mut state = CState::new();
    assert!(
        assign_call_result(
            &mut state,
            "temporary",
            value,
            &mut Vec::new(),
            &PureFactContext::new()
        )
        .is_ok()
    );
    assert!(matches!(
        state.locals.binding("temporary"),
        Some(CLocalBinding::Object {
            pointee_constant: true,
            ..
        })
    ));
}

#[test]
fn call_result_cannot_overwrite_reserved_mutex_storage() {
    let state = CState::new().with_local("result", int32(0));
    let pointer = state.locals.slot("result").unwrap().clone();
    let mut state = crate::kernel::mutexes::MutexContext::new(state)
        .initialize_empty(pointer, 40)
        .unwrap()
        .into_state();
    assert!(matches!(
        assign_call_result(
            &mut state,
            "result",
            int32(1),
            &mut Vec::new(),
            &PureFactContext::new()
        ),
        Err(CRuntimeError::MutexStorageWrite { .. })
    ));
}

#[test]
fn pointee_const_return_symbolic_callback_checks_signature_and_destination() {
    let template = CFunction::new(CType::Int32Pointer, "view", vec![], CStatement::Skip)
        .with_return_pointee_constant(true)
        .with_contract(vec![], vec![], vec![], vec![], true);
    let contract = CFunctionContract::new("View", template).unwrap();
    let qualified = contract.function_pointer_type();
    let unqualified =
        CType::FunctionPointer(CType::function_pointer_signature(CType::Int32Pointer, &[]));
    let pointer = Pointer {
        block: PointerBlock::FunctionSymbolic(Variable(890)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = CValue::typed_pointer(pointer.clone(), qualified);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Predicate {
        name: contract.predicate_name(),
        arguments: vec![
            Term::CState(Box::new(CState::new().with_population_creation_tracking())),
            Term::CValue(value),
        ],
    });
    let environment = CExecutionEnvironment::new().with_function_contract(contract);
    for (signature, mutable_destination) in
        [(qualified, false), (qualified, true), (unqualified, false)]
    {
        let mut state = CState::new()
            .with_population_creation_tracking()
            .with_local(
                "callback",
                CValue::typed_pointer(pointer.clone(), signature),
            );
        if mutable_destination {
            state = state.with_local(
                "temporary",
                CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
            );
        }
        let paths = execute_c_call_assign_paths(
            &state,
            "temporary",
            "callback",
            &[],
            &assumptions,
            CExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        if signature == qualified && !mutable_destination {
            assert!(matches!(&paths[0].outcome, CStatementOutcome::Normal(state)
                    if matches!(state.locals.binding("temporary"), Some(CLocalBinding::Object { value: CValue::Pointer(pointer), pointee_constant: true, .. }) if pointer.pointee_constant())));
        } else {
            assert!(matches!(
                &paths[0].outcome,
                CStatementOutcome::RuntimeError(_)
            ));
        }
    }
}
