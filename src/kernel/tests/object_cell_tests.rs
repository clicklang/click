//! Values of an abstract type in an allocation of the type's size: the
//! spike for whole-object cells of symbolic extent.
use super::*;

/// One step of `statement` from `state`, which must end normally.
fn step(state: &ExecutionState, statement: &ProgramStatement, facts: &PureFactContext) -> ExecutionState {
    let paths = execute_execution_statement_paths(
        state,
        statement,
        facts,
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::default(),
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    match &paths[0].outcome {
        StatementOutcome::Normal(next) => (**next).clone(),
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_value_of_an_abstract_type_lives_in_an_allocation_of_its_size() {
    let parameter = TypeParameterName::intern("ObjectCellT");
    let size = parameter.size_term();
    let value = AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::Variable(Variable(99_101)),
    };
    // What every size of a type that occupies memory satisfies: positive,
    // and at most `PTRDIFF_MAX`.
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::uint64_greater_than(size.clone(), MachineTerm::uint64_constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::uint64_less_equal(
                size.clone(),
                MachineTerm::uint64_constant(i64::MAX as u64),
            ),
            true,
        );
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(Address::null()))
        .with_local("n", ProgramValue::UInt64(size.clone()))
        .with_local("x", ProgramValue::Parameter(Box::new(value.clone())));
    let allocated = step(
        &state,
        &program_heap_allocate_sized_with_zeroed(
            "p",
            crate::kernel::program_expression::variable("n"),
            false,
        ),
        &facts,
    );
    let local = allocated.locals().get_native("p");
    let Some(ProgramValue::Pointer(pending)) = local.as_deref() else {
        panic!("allocation assigns a pointer");
    };
    let allocated = resolve_pending_heap_allocations(
        &allocated,
        &facts.clone().assume_proposition(Proposition::condition_is(
            ConditionTerm::address_equal(pending.address().clone(), Address::null()),
            false,
        )),
    );
    let object = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::variable("p"),
        ProgramType::ParameterPointer(parameter),
    );
    let stored = step(
        &allocated,
        &program_typed_store(
            object.clone(),
            crate::kernel::program_expression::variable("x"),
            ProgramType::Parameter(parameter),
        ),
        &facts,
    );
    let read = evaluate_program_expression_paths(
        &stored,
        &crate::kernel::program_expression::typed_load(object, ProgramType::Parameter(parameter)),
        &facts,
        &mut ExecutionBudget::default(),
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    assert!(
        matches!(
            read.as_slice(),
            [ExpressionPath { outcome: ExpressionOutcome::Value(ProgramValue::Parameter(read)), .. }]
                if **read == value
        ),
        "{read:?}"
    );
}
