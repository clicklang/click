use super::*;
// Surface planning; only this test reaches it from inside the kernel.

#[test]
fn pointee_const_return_rebinding_is_allowed_but_store_through_pointer_is_not() {
    let value =
        ProgramValue::typed_pointer(Pointer::symbolic(Variable(916)), ProgramType::Int32Pointer);
    let mut state = ExecutionState::new().with_local("p", value.clone());
    state.locals.set_typed_with_all_qualifiers(
        "q",
        value,
        ProgramType::Int32Pointer,
        false,
        false,
        false,
        true,
    );
    let environment = ExecutionEnvironment::new();
    let paths = execute_c_statement_paths(
        &state,
        &c_assign("q", c_variable("p")),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let StatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("const pointee does not prohibit rebinding")
    };
    assert!(matches!(
        state.locals.binding("q"),
        Some(LocalBinding::Object {
            pointee_constant: true,
            ..
        })
    ));
    let paths = execute_c_statement_paths(
        state,
        &c_store(c_variable("q"), c_int32_literal(1)),
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn pointee_const_return_inline_call_preserves_pointer_identity() {
    let function = ProgramFunction::new(
        ProgramType::Int32Pointer,
        "view",
        vec![c_parameter("p", ProgramType::Int32Pointer)],
        c_return(c_variable("p")),
    )
    .with_return_pointee_constant(true)
    .with_inline_body();
    let value =
        ProgramValue::typed_pointer(Pointer::symbolic(Variable(917)), ProgramType::Int32Pointer);
    let state = ExecutionState::new().with_local("p", value.clone());
    let environment = ExecutionEnvironment::new().with_function(function);
    let paths = execute_c_call_assign_paths(
        &state,
        "temporary",
        "view",
        &[c_variable("p")],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let StatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("inline call must return")
    };
    let local_native_output_76 = state.locals.get_native("temporary");
    let result = local_native_output_76.as_deref().unwrap();
    assert!(matches!(result, ProgramValue::Pointer(pointer) if pointer.pointee_constant()));
    let equality =
        c_value_comparison_proposition(result, ComparisonOperator::Equal, &value).unwrap();
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &equality
    ));
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn pointee_const_return_direct_and_callback_calls_preserve_const() {
    let function = ProgramFunction::new(
        ProgramType::UInt8Pointer,
        "text",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_return_pointee_constant(true);
    let function_type = function.function_pointer_type();
    let environment = ExecutionEnvironment::new().with_function(function);
    let paths = execute_c_call_assign_paths(
        &ExecutionState::new(),
        "temporary",
        "text",
        &[],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { pointee_constant: true, .. }))));
    let state = ExecutionState::new().with_local(
        "callback",
        ProgramValue::typed_pointer(
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
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { pointee_constant: true, .. }))));

    let state = state.with_local(
        "mutable",
        ProgramValue::typed_pointer(Pointer::null(), ProgramType::UInt8Pointer),
    );
    let paths = execute_c_call_assign_paths(
        &state,
        "mutable",
        "callback",
        &[],
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
    ));

    let incompatible = ProgramType::FunctionPointer(ProgramType::function_pointer_signature(
        ProgramType::UInt8Pointer,
        &[],
    ));
    let state = ExecutionState::new().with_local(
        "callback",
        ProgramValue::typed_pointer(
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
        ExecutionContext::execute_bodies(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        &paths[0].outcome,
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(_))
    ));
}

#[test]
fn pointee_const_return_assignment_preserves_destination_and_temporary_qualifiers() {
    for source_const in [false, true] {
        for destination_const in [false, true] {
            for immutable in [false, true] {
                let value = ProgramValue::typed_pointer(
                    Pointer::symbolic(Variable(912)),
                    ProgramType::UInt8Pointer,
                )
                .with_pointer_pointee_constant(source_const);
                let mut state = ExecutionState::new();
                state.locals.set_typed_with_all_qualifiers(
                    "text",
                    value.clone(),
                    ProgramType::UInt8Pointer,
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
                        matches!(state.locals.binding("text"), Some(LocalBinding::Object { value, pointee_constant, .. })
                            if *pointee_constant == destination_const && value.pointer().is_some_and(|pointer| pointer.pointee_constant() == destination_const))
                    );
                }
            }
        }
    }
    let value =
        ProgramValue::typed_pointer(Pointer::symbolic(Variable(913)), ProgramType::UInt8Pointer)
            .with_pointer_pointee_constant(true);
    let mut state = ExecutionState::new();
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
        Some(LocalBinding::Object {
            pointee_constant: true,
            ..
        })
    ));
}

#[test]
fn call_result_cannot_overwrite_reserved_mutex_storage() {
    let state = ExecutionState::new().with_local("result", int32(0));
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
        Err(RuntimeError::MutexStorageWrite { .. })
    ));
}

#[test]
fn pointee_const_return_symbolic_callback_checks_signature_and_destination() {
    let template = ProgramFunction::new(
        ProgramType::Int32Pointer,
        "view",
        vec![],
        ProgramStatement::Skip,
    )
    .with_return_pointee_constant(true)
    .with_contract(vec![], vec![], vec![], vec![], true);
    let contract = FunctionContract::new("View", template).unwrap();
    let qualified = contract.function_pointer_type();
    let unqualified = ProgramType::FunctionPointer(ProgramType::function_pointer_signature(
        ProgramType::Int32Pointer,
        &[],
    ));
    let pointer = Pointer {
        block: PointerBlock::FunctionSymbolic(Variable(890)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = ProgramValue::typed_pointer(pointer.clone(), qualified);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Predicate {
        name: contract.predicate_name(),
        arguments: vec![
            Term::ExecutionState(Box::new(
                ExecutionState::new().with_population_creation_tracking(),
            )),
            Term::ProgramValue(value),
        ],
    });
    let environment = ExecutionEnvironment::new().with_function_contract(contract);
    for (signature, mutable_destination) in
        [(qualified, false), (qualified, true), (unqualified, false)]
    {
        let mut state = ExecutionState::new()
            .with_population_creation_tracking()
            .with_local(
                "callback",
                ProgramValue::typed_pointer(pointer.clone(), signature),
            );
        if mutable_destination {
            state = state.with_local(
                "temporary",
                ProgramValue::typed_pointer(Pointer::null(), ProgramType::Int32Pointer),
            );
        }
        let paths = execute_c_call_assign_paths(
            &state,
            "temporary",
            "callback",
            &[],
            &assumptions,
            ExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        if signature == qualified && !mutable_destination {
            assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
                    if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { value, pointee_constant: true, .. }) if value.pointer().is_some_and(|pointer| pointer.pointee_constant()))));
        } else {
            assert!(matches!(
                &paths[0].outcome,
                StatementOutcome::RuntimeError(_)
            ));
        }
    }
}
