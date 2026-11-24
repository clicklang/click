use super::*;

#[test]
fn unindexed_boolean_loads_use_their_certified_observation_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let pointer = ProgramValue::typed_pointer(address.clone(), ProgramType::UInt8Pointer);
    let first = ExecutionState::new()
        .begin_function_entry_memory()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::access(address.clone(), ProgramType::Bool)),
        ));
    let second = first.clone().begin_function_entry_memory();
    assert_eq!(first.memory(), second.memory());

    let logical = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(pointer.clone())),
        value_type: ProgramType::Bool,
        exact: false,
    };
    let program = ProgramExpression::TypedLoad {
        pointer: Box::new(ProgramExpression::Value(pointer)),
        value_type: ProgramType::Bool,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let assumptions = PureFactContext::new();
    for state in [&first, &second] {
        let expected = ProgramValue::of_bool(ConditionTerm::boolean_cell_read(
            state.program_point().for_exact_read(),
            address.clone(),
        ));
        let mut execution = ExecutionBudget::new();
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(state, None),
            &logical,
            &assumptions,
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one logical Boolean read");
        };
        assert_eq!(path.value.clone().into_native(), expected);

        let paths = crate::kernel::eval::evaluate_expression_value_paths(
            state,
            &program,
            &assumptions,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one checked Boolean read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!(
                "the caller supplies a readable Boolean cell: {:?}",
                path.outcome
            );
        };
        assert_eq!(value.native().as_ref(), &expected);
    }
}

#[test]
fn caller_callback_reads_keep_the_entry_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let ty = ProgramType::FunctionPointer(ProgramType::function_pointer_signature(
        ProgramType::Int32,
        &[ProgramType::Int32],
    ));
    let entry = ExecutionState::new()
        .begin_function_entry_memory()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::access(address.clone(), ty)),
        ));
    let local = crate::kernel::SymbolicMemory::local_pointer("unrelated");
    let state = entry
        .clone()
        .with_memory(entry.memory().clone().with_block(local.base.clone(), 2));
    assert_ne!(entry.program_point_id(), state.observation_point_id());
    let pointer = ProgramValue::typed_pointer(address.clone(), ProgramType::UInt8Pointer);
    let check = |read: &ProgramValue| {
        let ProgramValue::Pointer(pointer) = read else {
            panic!("expected a complete callback read");
        };
        let load = pointer.address().as_loaded_value().expect("callback read");
        assert_eq!(load.point.read_version_id(), entry.program_point_id());
        assert_eq!(load.defining_address, address);
        // A callback read is the cell's one load, decoded as a function
        // pointer: the category is the term's, not the load's.
        assert!(load.identity.is_point_named());
        assert!(matches!(
            pointer.program_type(),
            ProgramType::FunctionPointer(_)
        ));
    };
    let assumptions = PureFactContext::new();
    let logical = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(pointer.clone())),
        value_type: ty,
        exact: false,
    };
    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&state, None),
        &logical,
        &assumptions,
        &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one logical callback read");
    };
    check(&path.value.clone().into_native());

    let program = ProgramExpression::TypedLoad {
        pointer: Box::new(ProgramExpression::Value(pointer)),
        value_type: ty,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let paths = crate::kernel::eval::evaluate_expression_value_paths(
        &state,
        &program,
        &assumptions,
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one checked callback read");
    };
    let ExpressionOutcome::Value(value) = &path.outcome else {
        panic!(
            "the caller supplies a readable callback: {:?}",
            path.outcome
        );
    };
    check(value.native().as_ref());

    check(&crate::kernel::eval::canonical_cell_value(
        &state.program_point(),
        &address,
        ty,
    ));
}

#[test]
fn caller_int16_reads_keep_the_entry_point() {
    assert_caller_integer_reads_keep_the_entry_point(&[ProgramType::Int16, ProgramType::UInt16]);
}

#[test]
fn caller_byte_reads_keep_the_entry_point() {
    assert_caller_integer_reads_keep_the_entry_point(&[ProgramType::Int8, ProgramType::UInt8]);
}

#[test]
fn caller_int64_reads_keep_the_entry_point() {
    assert_caller_integer_reads_keep_the_entry_point(&[ProgramType::Int64, ProgramType::UInt64]);
}

#[test]
fn caller_int128_reads_keep_the_entry_point() {
    assert_caller_integer_reads_keep_the_entry_point(&[ProgramType::Int128, ProgramType::UInt128]);
}

fn assert_caller_integer_reads_keep_the_entry_point(value_types: &[ProgramType]) {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
    };
    let local = crate::kernel::SymbolicMemory::local_pointer("unrelated");
    for &ty in value_types {
        let pointer_type = ty.pointer_to().unwrap();
        let entry = ExecutionState::new()
            .begin_function_entry_memory()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::view_memory(MemoryRange::access(address.clone(), ty)),
            ));
        let state = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(local.base.clone(), 2));
        assert_ne!(state.observation_point_id(), entry.program_point_id());
        let pointer = ProgramValue::typed_pointer(address.clone(), pointer_type);
        let kind = LoadKind::of_type(ty).unwrap();
        let check = |read: &ProgramValue| {
            let Some(MachineTerm::MemoryLoad(point, cell, load_kind)) =
                program_value_bitvector_term(read)
            else {
                panic!("expected a symbolic {ty:?} read");
            };
            assert_eq!(point.read_version_id(), entry.program_point_id());
            assert_eq!(*cell, address);
            assert_eq!(load_kind, kind);
        };
        let assumptions = PureFactContext::new();
        let logical = SpecExpression::MemoryLoad {
            point: SpecPoint::Current,
            pointer: Box::new(SpecExpression::Value(pointer.clone())),
            value_type: ty,
            exact: false,
        };
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&state, None),
            &logical,
            &assumptions,
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one logical caller read");
        };
        check(&path.value.clone().into_native());

        let program = ProgramExpression::Load(Box::new(ProgramExpression::Value(pointer)));
        let paths = crate::kernel::eval::evaluate_expression_value_paths(
            &state,
            &program,
            &assumptions,
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one checked caller read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("the caller supplies a readable cell: {:?}", path.outcome);
        };
        check(value.native().as_ref());

        let resource =
            crate::kernel::eval::canonical_cell_load(&state.program_point(), &address, ty);
        check(&crate::kernel::cell_run_value(ty, resource));
    }
}

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

#[test]
fn a_held_abstract_read_after_storage_havoc_keeps_its_point() {
    use crate::kernel::{AggregateLayout, TypeParameterName};
    let _session = crate::kernel::VerificationSession::enter();
    let slot = SymbolicMemory::local_pointer("abstract_output");
    let parameter = TypeParameterName::intern("AbstractOutputPoint");
    let value_type = ProgramType::Parameter(parameter);
    let bytes = value_type.byte_width();
    let mut before = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_block(slot.base.clone(), bytes)
            .store(
                slot.clone(),
                ProgramValue::Parameter(Box::new(AlgebraicTerm {
                    algebraic_type: parameter.algebraic_type(),
                    node: AlgebraicTermNode::Variable(Variable(1008311)),
                })),
            ),
    );
    before.locals.set_aggregate_object_at(
        "value",
        AggregateLayout::holding_value(value_type),
        slot.clone(),
    );
    let effect = MemoryRange::access(slot.clone(), value_type);
    let after = before.clone().with_memory(
        before
            .memory()
            .clone()
            .with_storage_memory_havoc(Variable(1008312), &[effect], &PureFactContext::new())
            .with_initialized_object(&slot, bytes),
    );
    assert_ne!(after.observation_point_id(), before.observation_point_id());
    let ProgramValue::Parameter(read) = after.held_local_value("value").unwrap() else {
        panic!("held abstract value");
    };
    let AlgebraicTermNode::MemoryLoad { point, pointer } = read.node else {
        panic!("the name reads the abstract object");
    };
    assert_eq!(point.read_version_id(), after.observation_point_id());
    assert_eq!(*pointer, slot);
}
