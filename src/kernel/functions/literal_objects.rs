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

#[test]
fn a_literal_span_is_checked_in_the_selected_memory() {
    let id = StringLiteralId::new("literal_span", 0);
    let pointer = SymbolicMemory::string_literal_pointer(&id, b"ok\0");
    let memory = SymbolicMemory::new().with_read_only_block(pointer.base.clone(), 3);
    let bytes = OldMachineTerm::Variable(Variable(92_001));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), bytes.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(bytes.clone(), 3u32.into()),
            true,
        );
    assert!(facts.proves_memory_loadable(&memory, &pointer, &bytes));
    assert!(!facts.proves_memory_loadable(&SymbolicMemory::new(), &pointer, &bytes));
    assert!(!facts.proves_memory_loadable(&memory, &pointer.offset_by_bytes(3), &1u32.into()));
    let alias = Address::symbolic(Variable(92_002));
    let facts = facts.assume_condition(
        ConditionTerm::address_equal(alias.clone(), pointer.clone()),
        true,
    );
    assert!(facts.proves_memory_loadable(&memory, &alias, &bytes));

    let wide = OldMachineTerm::Variable(Variable(92_003));
    let facts = facts.assume_condition(
        ConditionTerm::uint64_less_equal(wide.clone(), OldMachineTerm::uint64_constant(3)),
        true,
    );
    assert!(facts.proves_native_memory_loadable(&memory, &pointer, &wide));
    assert!(!facts.proves_native_memory_loadable(&SymbolicMemory::new(), &pointer, &wide));
}

mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/functions/literal_objects.rs");
}
