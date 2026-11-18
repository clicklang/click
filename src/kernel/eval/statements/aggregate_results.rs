use super::*;
use crate::kernel::VerificationSession;

fn fixture(fields: u32) -> (ExecutionState, ProgramExpression, AggregateLayout) {
    let source = SymbolicMemory::local_pointer("source");
    let layout = AggregateLayout::new(
        fields * 8,
        8,
        (0..fields)
            .map(|i| AggregateField::new(format!("field{i}"), i * 8, ProgramType::Int32))
            .collect(),
    );
    let mut memory =
        SymbolicMemory::new().with_uninitialized_block(source.base.clone(), layout.size_bytes());
    for i in 0..fields {
        memory = memory.store(source.offset_by_bytes(i * 8), int32(i));
    }
    let state = ExecutionState::new().with_memory(memory);
    (
        state,
        ProgramExpression::Value(ProgramValue::typed_pointer(
            source,
            ProgramType::UInt8Pointer,
        )),
        layout,
    )
}

fn materialize(
    state: &ExecutionState,
    source: &ProgramExpression,
    layout: &AggregateLayout,
    budget: &mut ExecutionBudget,
) -> ExecutionState {
    let mut paths = execute_program_aggregate_step_paths(
        state,
        &[0],
        source,
        &AggregateResultLayout {
            layout: layout.clone(),
            declared_class: None,
        },
        &PureFactContext::default(),
        budget,
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    match paths.pop().unwrap().outcome {
        StatementOutcome::Normal(state) => *state,
        outcome => panic!("aggregate result: {outcome:?}"),
    }
}

#[test]
fn aggregate_results_have_anonymous_storage_and_end_with_their_expression() {
    let _session = VerificationSession::enter();
    let (state, source, layout) = fixture(2);
    let mut budget = ExecutionBudget::for_new_execution();
    let result = materialize(&state, &source, &layout, &mut budget);
    let pointer = result.aggregate_step_objects.get(&0).unwrap().clone();
    assert!(matches!(pointer.base, AddressBase::Temporary(_)));
    assert_eq!(
        result.memory.known_value(&pointer.offset_by_bytes(8)),
        Some(int32(1))
    );
    assert_eq!(result.locals, state.locals);
    let store = crate::kernel::program_typed_store(
        ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::Int32Pointer,
        )),
        ProgramExpression::Value(int32(12)),
        ProgramType::Int32,
    );
    assert!(matches!(
        execute_execution_statement(&result, &store, &PureFactContext::default()),
        Some(StatementOutcome::UndefinedBehavior(_))
    ));

    let ended = end_aggregate_step_lifetimes(&result, &[0]).unwrap();
    assert!(!ended.memory.has_block(&pointer.base));
    assert!(ended.step_result(0).is_none());
    assert!(ended.aggregate_step_objects.is_empty());
    let read =
        crate::kernel::program_return(ProgramExpression::Load(Box::new(ProgramExpression::Value(
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        ))));
    assert!(matches!(
        execute_execution_statement(&ended, &read, &PureFactContext::default()),
        Some(StatementOutcome::UndefinedBehavior(_))
    ));
    // A historical result keeps its own state; re-execution allocates a new object.
    assert!(result.memory.has_block(&pointer.base));
    let again = materialize(&ended, &source, &layout, &mut budget);
    assert_ne!(&pointer, again.aggregate_step_objects.get(&0).unwrap());
}

#[test]
fn aggregate_result_copies_pointer_fields_without_copying_or_retiring_the_pointee() {
    let _session = VerificationSession::enter();
    let backing = SymbolicMemory::local_pointer("backing");
    let source = SymbolicMemory::local_pointer("source");
    let value = ProgramValue::typed_pointer(backing.clone(), ProgramType::Int32Pointer);
    let layout = AggregateLayout::new(
        8,
        8,
        vec![AggregateField::new("data", 0, ProgramType::Int32Pointer)],
    );
    let state = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_block(backing.base.clone(), 4)
            .store(backing.clone(), int32(9))
            .with_block(source.base.clone(), 8)
            .store(source.clone(), value.clone()),
    );
    let copied = materialize(
        &state,
        &ProgramExpression::Value(ProgramValue::typed_pointer(
            source,
            ProgramType::UInt8Pointer,
        )),
        &layout,
        &mut ExecutionBudget::for_new_execution(),
    );
    let destination = copied.aggregate_step_objects.get(&0).unwrap();
    assert_eq!(copied.memory.known_value(destination), Some(value));
    let ended = end_aggregate_step_lifetimes(&copied, &[0]).unwrap();
    assert_eq!(ended.memory.known_value(&backing), Some(int32(9)));
    assert!(ended.memory.has_block(&backing.base));
}

#[test]
fn aggregate_result_rejects_an_uninitialized_source_field() {
    let _session = VerificationSession::enter();
    let (mut state, source, layout) = fixture(2);
    state.set_memory(
        SymbolicMemory::new()
            .with_uninitialized_block("local:source", 16)
            .store(SymbolicMemory::local_pointer("source"), int32(0)),
    );
    let paths = execute_program_aggregate_step_paths(
        &state,
        &[0],
        &source,
        &AggregateResultLayout {
            layout: layout.clone(),
            declared_class: None,
        },
        &PureFactContext::default(),
        &mut ExecutionBudget::for_new_execution(),
    )
    .unwrap();
    assert!(matches!(
        paths[0].outcome,
        StatementOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
    ));
}

#[test]
fn aggregate_array_field_decay_keeps_the_element_pointer_type() {
    let _session = VerificationSession::enter();
    let source = SymbolicMemory::local_pointer("array");
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 16));
    let pointer = ProgramValue::typed_pointer(source, ProgramType::UInt8Pointer)
        .with_pointer_pointee_constant(true);
    for (array_type, pointer_type) in [
        (ProgramType::Int32Array(2), ProgramType::Int32Pointer),
        (ProgramType::Float64Array(2), ProgramType::Float64Pointer),
    ] {
        let expression = crate::kernel::program_expression::typed_load(
            ProgramExpression::Value(pointer.clone()),
            array_type,
        );
        let paths = evaluate_program_expression_paths(
            &state,
            &expression,
            &PureFactContext::default(),
            &mut ExecutionBudget::for_new_execution(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].outcome,
            ExpressionOutcome::Value(pointer.clone().retag_pointer(pointer_type))
        );
    }
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/eval/statements/aggregate_results.rs");
}

#[test]
fn loop_test_retires_aggregate_storage_on_true_and_false_outcomes() {
    let _session = VerificationSession::enter();
    let (state, source, layout) = fixture(2);
    let result = materialize(
        &state,
        &source,
        &layout,
        &mut ExecutionBudget::for_new_execution(),
    );
    let pointer = result.aggregate_step_objects.get(&0).unwrap().clone();
    for truth in [false, true] {
        let statement = ProgramStatement::LoopTest {
            condition: crate::kernel::program_expression::int32_literal(u32::from(truth)),
            aggregate_steps: vec![0],
        };
        let outcome = execute_execution_statement(&result, &statement, &PureFactContext::default())
            .expect("the condition and its cleanup have one successor");
        let ended = match (truth, outcome) {
            (true, StatementOutcome::Normal(state))
            | (false, StatementOutcome::LoopTestFalse(state)) => state,
            (_, outcome) => panic!("unexpected test outcome {outcome:?}"),
        };
        assert!(!ended.memory.has_block(&pointer.base));
        assert!(ended.aggregate_step_objects.is_empty());
        assert!(ended.step_result(0).is_none());
    }
    assert!(
        result.memory.has_block(&pointer.base),
        "each decision forks the original state"
    );
}
