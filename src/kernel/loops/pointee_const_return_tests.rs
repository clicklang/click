use super::*;
// Surface planning; only this test reaches it from inside the kernel.

#[test]
fn pointee_const_rebinding_keeps_the_destinations_declared_qualifier() {
    let value =
        ProgramValue::typed_pointer(Address::symbolic(Variable(916)), ProgramType::Int32Pointer);
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
    let paths = execute_execution_statement_paths(
        &state,
        &program_assign("q", crate::kernel::program_expression::variable("p")),
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&environment),
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
}

#[test]
fn pointee_const_return_inline_call_preserves_pointer_identity() {
    let function = ProgramFunction::new(
        ProgramType::Int32Pointer,
        "view",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_return(crate::kernel::program_expression::variable("p")),
    )
    .with_return_pointee_constant(true)
    .with_inline_body();
    let value =
        ProgramValue::typed_pointer(Address::symbolic(Variable(917)), ProgramType::Int32Pointer);
    let state = ExecutionState::new().with_local("p", value.clone());
    let environment = ExecutionEnvironment::new().with_function(function);
    let paths = call_then_assign_paths(
        ProgramType::Int32Pointer,
        &state,
        "temporary",
        "view",
        &[crate::kernel::program_expression::variable("p")],
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
    assert!(matches!(result, ProgramValue::Pointer(_)));
    let equality =
        program_value_comparison_proposition(result, ComparisonOperator::Equal, &value).unwrap();
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
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_return_pointee_constant(true);
    let function_type = function.function_pointer_type();
    let environment = ExecutionEnvironment::new().with_function((function).with_inline_body());
    let paths = call_then_assign_paths(
        ProgramType::UInt8Pointer,
        &ExecutionState::new(),
        "temporary",
        "text",
        &[],
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { pointee_constant: true, .. }))));
    let state = ExecutionState::new().with_local(
        "callback",
        ProgramValue::typed_pointer(
            Address::new(
                AddressBase::Function("text".to_string()),
                AddressOffset::constant(0),
            ),
            function_type,
        ),
    );
    let paths = call_then_assign_paths(
        ProgramType::UInt8Pointer,
        &state,
        "temporary",
        "callback",
        &[],
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&environment),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
            if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { pointee_constant: true, .. }))));

    let incompatible = ProgramType::FunctionPointer(ProgramType::function_pointer_signature(
        ProgramType::UInt8Pointer,
        &[],
    ));
    let state = ExecutionState::new().with_local(
        "callback",
        ProgramValue::typed_pointer(
            Address::new(
                AddressBase::Function("text".into()),
                AddressOffset::constant(0),
            ),
            incompatible,
        ),
    );
    let paths = call_then_assign_paths(
        ProgramType::UInt8Pointer,
        &state,
        "temporary",
        "callback",
        &[],
        &PureFactContext::new(),
        ExecutionContext::verify_loops(&environment),
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
    {
        for destination_const in [false, true] {
            for immutable in [false, true] {
                let value = ProgramValue::typed_pointer(
                    Address::symbolic(Variable(912)),
                    ProgramType::UInt8Pointer,
                );
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
                    &("text").into(),
                    value,
                    &mut Vec::new(),
                    &PureFactContext::new(),
                );
                // Whether a pointer may drop `const` is the frontend's C type
                // check; the kernel refuses only an immutable destination.
                assert_eq!(result.is_ok(), !immutable);
                if result.is_ok() {
                    assert!(
                        matches!(state.locals.binding("text"), Some(LocalBinding::Object { pointee_constant, .. })
                            if *pointee_constant == destination_const)
                    );
                }
            }
        }
    }
    let value =
        ProgramValue::typed_pointer(Address::symbolic(Variable(913)), ProgramType::UInt8Pointer);
    let mut state = ExecutionState::new();
    assert!(
        assign_call_result(
            &mut state,
            &("temporary").into(),
            value,
            &mut Vec::new(),
            &PureFactContext::new()
        )
        .is_ok()
    );
    // A new temporary's qualifiers come from its declaration, not from the
    // value it receives.
    assert!(matches!(
        state.locals.binding("temporary"),
        Some(LocalBinding::Object {
            pointee_constant: false,
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
            &("result").into(),
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
    let pointer = Address::new(
        AddressBase::FunctionSymbolic(Variable(890)),
        AddressOffset::constant(0),
    );
    let value = ProgramValue::typed_pointer(pointer.clone(), qualified);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Predicate {
        name: contract.predicate_name(),
        arguments: vec![
            Term::ExecutionState(Box::new(
                ExecutionState::new().with_population_creation_tracking(),
            )),
            Term::ProgramValue((value).into()),
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
                ProgramValue::typed_pointer(Address::null(), ProgramType::Int32Pointer),
            );
        }
        let paths = call_then_assign_paths(
            ProgramType::Int32Pointer,
            &state,
            "temporary",
            "callback",
            &[],
            &assumptions,
            ExecutionContext::verify_loops(&environment),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        if signature == qualified && !mutable_destination {
            assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(state)
                    if matches!(state.locals.binding("temporary"), Some(LocalBinding::Object { pointee_constant: true, .. }))));
        } else if signature == qualified {
            assert!(matches!(&paths[0].outcome, StatementOutcome::Normal(_)));
        } else {
            assert!(matches!(
                &paths[0].outcome,
                StatementOutcome::RuntimeError(_)
            ));
        }
    }
}

fn call_then_assign_paths(
    result_type: ProgramType,
    state: &ExecutionState,
    target: &str,
    function_name: &str,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let call_and_assignment =
        program_call_then_assign(0, target, function_name, arguments.to_vec());
    let statement = if state.locals.binding(target).is_none() {
        program_seq(
            program_declare_with_all_qualifiers(target, result_type, false, false, false, true),
            call_and_assignment,
        )
    } else {
        call_and_assignment
    };
    execute_execution_statement_paths(state, &statement, assumptions, execution_context, budget)
}
