use super::*;

#[test]
fn logical_pointer_field_uses_current_pointee_memory() {
    use crate::kernel::{AggregateField, AggregateLayout};
    let slot = Address {
        base: "local:frame:0:input".into(),
        offset: AddressOffset::Constant(0),
    };
    let pointee = Address {
        base: "local:pointee".into(),
        offset: AddressOffset::Constant(0),
    };
    let mut entry = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_block(slot.base.clone(), 8)
            .with_block(pointee.base.clone(), 4)
            .store(slot.clone(), ProgramValue::pointer(pointee.clone()))
            .store(pointee.clone(), int32(3)),
    );
    entry.locals.set_aggregate_object_at(
        "input".to_string(),
        AggregateLayout::new(
            8,
            8,
            vec![AggregateField::new("data", 0, ProgramType::Int32Pointer)],
        ),
        slot.clone(),
    );
    let load = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::AggregateFieldValue {
            parameter: "input".to_string().into(),
            pointer: Box::new(SpecExpression::ProgramExpression(
                ProgramExpression::Variable(("input".to_string()).into()),
            )),
            value_type: ProgramType::Int32Pointer,
        }),
        value_type: ProgramType::Int32,
        exact: false,
    };
    let state = entry.clone().with_memory(
        entry
            .memory
            .clone()
            .without_local_block(&slot.base)
            .store(pointee.clone(), int32(7)),
    );
    let evaluate = |state: &ExecutionState| {
        evaluate_spec_expression_paths_with_loop_entry_in(
            state,
            &load,
            Some(&entry),
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
        )
        .unwrap()
    };
    let paths = evaluate(&state);
    assert_eq!(paths.len(), 1);
    assert_eq!(
        crate::kernel::eval::read_over_write_program_value(&paths[0].value.clone().into_native()),
        int32(7)
    );
    assert!(paths[0].obligations.is_empty());
    let ended = state
        .clone()
        .with_memory(state.memory.clone().without_local_block(&pointee.base));
    let paths = evaluate(&ended);
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    assert!(!PureFactContext::new().proves_memory_read_defined(
        ended.memory(),
        &pointee,
        ProgramType::Int32,
    ));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/aggregate_value_tests.rs");
}

#[test]
fn held_abstract_loads_keep_their_store_point_in_equality() {
    use crate::kernel::{AggregateLayout, TypeParameterName};
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address {
        base: "local:abstract-slot".into(),
        offset: AddressOffset::Constant(0),
    };
    let parameter = TypeParameterName::intern("PointNamedLocal");
    let value_type = ProgramType::Parameter(parameter);
    let mut start = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_block(slot.base.clone(), value_type.byte_width())
            .with_block("local:unrelated", 4),
    );
    start.locals.set_aggregate_object_at(
        "value",
        AggregateLayout::holding_value(value_type),
        slot.clone(),
    );
    let store = |state: &ExecutionState, variable| {
        state.clone().with_memory(state.memory().clone().store(
            slot.clone(),
            ProgramValue::Parameter(Box::new(AlgebraicTerm {
                algebraic_type: parameter.algebraic_type(),
                node: AlgebraicTermNode::Variable(Variable(variable)),
            })),
        ))
    };
    let left = store(&store(&start, 1008201), 1008203);
    let right = store(&store(&start, 1008202), 1008203);
    assert_eq!(left.memory(), right.memory());
    let read = |state: &ExecutionState| {
        let ProgramValue::Parameter(value) = state.held_local_value("value").unwrap() else {
            panic!("held abstract load");
        };
        value
    };
    let first = read(&left);
    let second = read(&right);
    assert_ne!(first, second);
    let mut import = crate::kernel::KernelTermImport::default();
    let roots = [import.algebraic(&first), import.algebraic(&second)];
    assert_ne!(roots[0], roots[1]);
    assert!(!roots[0].algebraic_syntax_equal(&roots[1]));
    let AlgebraicTermNode::MemoryLoad { point, .. } = &first.node else {
        panic!("the held local names its defining write");
    };
    assert_eq!(point.read_version_id(), left.observation_point_id());
    let disjoint = left.clone().with_memory(left.memory().clone().store(
        Address {
            base: "local:unrelated".into(),
            offset: AddressOffset::Constant(0),
        },
        int32(7),
    ));
    assert_eq!(read(&disjoint), first);
    let mut graph = crate::kernel::equality_graph::EqualityGraph::default();
    assert!(!graph.are_algebraic_equal(&first, &second));
    assert!(graph.add_algebraic_equality(&first, &second));
    assert!(graph.are_algebraic_equal(&first, &second));
}
