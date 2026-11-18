use super::*;

#[test]
fn string_literal_objects_do_not_create_local_bindings() {
    let id = StringLiteralId::new("literal_object", 0);
    let function = program_function(
        ProgramType::Void,
        "literal_object",
        vec![],
        ProgramStatement::Skip,
    )
    .with_string_literals(vec![StringLiteral::new(id.clone(), b"ok\0".to_vec())]);
    let state = initialize_program_function_globals(&ExecutionState::new(), &function);
    assert!(state.locals.is_empty());
    let stored = state.literal_values.get(&id).expect("literal object");
    let pointer = stored.pointer().unwrap().address();
    assert!(state.memory.is_read_only_block(&pointer.base));
    assert_eq!(state.memory.block_size(&pointer.base), Some(&3.into()));
    let expression = ProgramExpression::StringLiteral(id);
    let paths = crate::kernel::eval::evaluate_expression_value_paths(
        &state,
        &expression,
        &PureFactContext::default(),
        &mut ExecutionBudget::for_new_execution(),
    )
    .unwrap();
    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
        panic!("literal value")
    };
    assert_eq!(value.shared(), stored.shared());
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/functions/literal_objects.rs");
}
