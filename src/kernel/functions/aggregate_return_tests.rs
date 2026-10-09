//! Compatibility oracles for the existing field-copy result mode. These do
//! not claim that C++ returned construction or destination forwarding is admitted.
use super::*;

fn node_layout() -> CAggregateLayout {
    CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("self", 0, CType::Int32Pointer),
            CAggregateField::new("value", 8, CType::Int32),
        ],
    )
}

fn copy_function() -> CFunction {
    c_function(
        CType::VoidPointer,
        "copy_result",
        vec![c_parameter("source", CType::VoidPointer)],
        c_return(c_variable("source")),
    )
    .with_return_aggregate_layout(node_layout())
}

fn pointer(value: &CValue) -> Pointer {
    let CValue::Pointer(value) = value else {
        panic!("expected an aggregate storage pointer");
    };
    value.pointer().clone()
}

fn destination_procedure(name: &str, body: CStatement) -> CFunction {
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("destination"),
        c_int32_literal(0),
        c_int32_literal(4),
    ));
    c_function(
        CType::Void,
        name,
        vec![
            c_parameter("destination", CType::Int32Pointer),
            c_parameter("input", CType::Int32),
        ],
        c_seq(body, c_return(c_void_value())),
    )
    .with_resource_summary(vec![storage.clone()], vec![storage])
}

// This tests the existing explicit-destination procedure building block,
// without the legacy placeholder-seeding declaration. It does not pass a
// supplied destination off as a by-value aggregate result.
#[test]
fn supplied_constructor_destination_survives_two_procedure_boundaries() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = c_pointer_offset_bytes(c_variable("destination"), 8);
    let constructor = destination_procedure(
        "initialize_node",
        c_seq(
            c_typed_store(
                c_variable("destination"),
                field.clone(),
                CType::Int32Pointer,
            ),
            c_typed_store(field, c_variable("input"), CType::Int32),
        ),
    );
    let forward = destination_procedure(
        "forward_node",
        c_call(
            "initialize_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let outer = destination_procedure(
        "outer_node",
        c_call(
            "forward_node",
            vec![c_variable("destination"), c_variable("input")],
        ),
    );
    let destination = CMemory::frame_local_pointer(100, "caller_node");
    let memory = CMemory::new().with_block(destination.block.clone(), 16);
    assert!(!memory.has_initialized_bytes_at(&destination, 16));
    let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
        CMemoryRange::new(destination.clone(), 0u32.into(), 4u32.into()),
    ));
    let caller = CState::new()
        .with_memory(memory)
        .with_resource_context(resources);
    let paths = execute_c_function_call_paths(
        &caller,
        &outer,
        &[c_pointer_value(destination.clone()), c_int32_literal(37)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new()
            .with_function(constructor)
            .with_function(forward),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("forwarded constructor execution");
    let [path] = paths.as_slice() else {
        panic!("one constructor path expected");
    };
    let CFunctionOutcome::Return { value, state } = &path.outcome else {
        panic!("constructor failed: {:?}", path.outcome);
    };
    assert_eq!(*value, CValue::Void);
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    assert_eq!(
        state.memory.known_value(&destination),
        Some(CValue::typed_pointer(
            destination.offset_by_bytes(8),
            CType::Int32Pointer,
        )),
    );
    assert_eq!(
        state.memory.known_value(&destination.offset_by_bytes(8)),
        Some(CValue::Int32(Bitvector32Term::Constant(37))),
    );
    assert_eq!(state.next_local_frame, caller.next_local_frame);
    assert!(state.memory.has_block(&destination.block));
}

// C++ copy-assignment coverage does not exercise the function return
// materializer. A future destination-return path must not silently change
// this existing copy mode to rebase self-pointers or elide its copies.
#[test]
fn aggregate_copy_return_preserves_self_pointer_through_two_materializations() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "node");
    let self_pointer = CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer);
    let memory = CMemory::new()
        .with_block(source.block.clone(), 16)
        .store(source.clone(), self_pointer.clone())
        .store(
            source.offset_by_bytes(8),
            CValue::Int32(Bitvector32Term::Constant(37)),
        );
    let mut state = CState::new().with_memory(memory);
    let function = copy_function();
    let first = materialize_aggregate_return(
        &mut state,
        &function,
        CValue::typed_pointer(source.clone(), CType::VoidPointer),
    )
    .expect("first copy result");
    let second = materialize_aggregate_return(&mut state, &function, first.clone())
        .expect("second copy result");
    assert_ne!(pointer(&first).block, source.block);
    assert_ne!(pointer(&second).block, pointer(&first).block);
    for result in [&first, &second] {
        let result = pointer(result);
        assert_eq!(
            state.memory.known_value(&result),
            Some(self_pointer.clone())
        );
        assert_ne!(pointer(&self_pointer), result.offset_by_bytes(8));
        assert_eq!(
            state.memory.known_value(&result.offset_by_bytes(8)),
            Some(CValue::Int32(Bitvector32Term::Constant(37))),
        );
    }
}

// Retiring a copied descriptor's callee-local source must distinguish a
// self-pointer from an external backing pointer. Keeping the result alive
// must neither rescue the former allocation nor retire the latter.
#[test]
fn aggregate_copy_return_retirement_preserves_only_independently_live_backing() {
    for points_to_self in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = CMemory::frame_local_pointer(100, "descriptor");
        let backing = CMemory::frame_local_pointer(101, "caller_backing");
        let caller = CMemory::new().with_block(backing.block.clone(), 4).store(
            backing.clone(),
            CValue::Int32(Bitvector32Term::Constant(23)),
        );
        let referent = if points_to_self {
            source.offset_by_bytes(8)
        } else {
            backing.clone()
        };
        let field = CValue::typed_pointer(referent.clone(), CType::Int32Pointer);
        let memory = caller
            .clone()
            .with_block(source.block.clone(), 16)
            .store(source.clone(), field.clone())
            .store(
                source.offset_by_bytes(8),
                CValue::Int32(Bitvector32Term::Constant(23)),
            );
        let mut state = CState::new().with_memory(memory);
        state.locals.set_aggregate_object_at(
            "descriptor".to_string(),
            node_layout(),
            source.clone(),
        );
        let function = copy_function();
        let result = materialize_aggregate_return(
            &mut state,
            &function,
            CValue::typed_pointer(source.clone(), CType::VoidPointer),
        )
        .expect("copy result");
        set_function_result(&mut state, &function, result.clone());
        let memory =
            end_function_body_automatic_lifetimes(&state, &function, &caller, Some(&result))
                .expect("callee retirement");
        assert!(!memory.has_block(&source.block));
        assert!(memory.has_block(&pointer(&result).block));
        assert!(memory.has_block(&backing.block));
        assert_eq!(memory.known_value(&pointer(&result)), Some(field));
        assert_eq!(memory.has_block(&referent.block), !points_to_self);
        assert_eq!(
            memory.known_value(&backing),
            Some(CValue::Int32(Bitvector32Term::Constant(23))),
        );
    }
}

// Modular field-copy results intentionally have fresh identities. The new
// construction mode needs a different binding; changing this helper globally
// would break existing C framing and would conceal destination aliasing.
#[test]
fn aggregate_copy_symbolic_result_has_a_fresh_identity_per_call() {
    let _session = crate::kernel::VerificationSession::enter();
    let function = copy_function();
    let first = symbolic_contract_result(function.contract_interface(), Variable(870_001));
    let second = symbolic_contract_result(function.contract_interface(), Variable(870_002));
    assert!(matches!(pointer(&first).block, PointerBlock::Temporary(_)));
    assert!(matches!(pointer(&second).block, PointerBlock::Temporary(_)));
    assert_ne!(pointer(&first).block, pointer(&second).block);
}

// Return completion must reject before allocating a result or copying any
// prefix. The two body-completion paths must not supply separate, drifting
// checks for this precondition.
#[test]
fn aggregate_copy_return_refuses_partial_initialization_without_changing_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CMemory::frame_local_pointer(100, "partial");
    let mut state =
        CState::new().with_memory(CMemory::new().with_block(source.block.clone(), 16).store(
            source.clone(),
            CValue::typed_pointer(source.offset_by_bytes(8), CType::Int32Pointer),
        ));
    let before = state.clone();
    assert_eq!(
        materialize_aggregate_return(
            &mut state,
            &copy_function(),
            CValue::typed_pointer(source, CType::VoidPointer),
        ),
        Err(AggregateReturnRefusal::UninitializedRead),
    );
    assert_eq!(state, before);
}
