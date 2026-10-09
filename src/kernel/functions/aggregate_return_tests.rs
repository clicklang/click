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
