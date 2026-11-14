use super::*;

fn normal(state: ExecutionState, statement: ProgramStatement) -> ExecutionState {
    let theorem = prove_execution_statement_execution(state, statement).unwrap();
    let Proposition::ProgramStatementExecutes {
        outcome: StatementOutcome::Normal(after),
        ..
    } = theorem.proposition()
    else {
        panic!("{:?}", theorem.proposition());
    };
    *after.clone()
}

fn outcome(state: &ExecutionState, expression: ProgramExpression) -> ExpressionOutcome {
    let theorem = prove_program_expression_evaluation(state.clone(), expression).unwrap();
    let Proposition::ProgramExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

fn value(state: &ExecutionState, expression: ProgramExpression) -> ProgramValue {
    match outcome(state, expression) {
        ExpressionOutcome::Value(value) => value,
        other => panic!("expected a value: {other:?}"),
    }
}

fn element_address(index: u32) -> ProgramExpression {
    ProgramExpression::AddressOf(Box::new(crate::kernel::program_expression::index(
        crate::kernel::program_expression::variable("items"),
        crate::kernel::program_expression::int32_literal(index),
    )))
}

#[test]
fn wide_address_scalar_address_and_pointer_slot_preserve_type_and_payload() {
    for (ty, pointer_ty, slot_ty, literal) in [
        (
            ProgramType::Int128,
            ProgramType::Int128Pointer,
            ProgramType::Int128PointerPointer,
            crate::kernel::program_expression::int128_literal(i128::MIN),
        ),
        (
            ProgramType::UInt128,
            ProgramType::UInt128Pointer,
            ProgramType::UInt128PointerPointer,
            crate::kernel::program_expression::uint128_literal(u128::MAX),
        ),
    ] {
        let expected = value(&ExecutionState::new(), literal.clone());
        let state = normal(
            ExecutionState::new(),
            program_seq(
                program_declare("wide", ty),
                program_seq(
                    program_assign("wide", literal),
                    program_seq(
                        program_declare("p", pointer_ty),
                        program_assign("p", crate::kernel::program_expression::addr_of("wide")),
                    ),
                ),
            ),
        );
        let pointer = value(&state, crate::kernel::program_expression::variable("p"));
        assert_eq!(pointer.program_type(), pointer_ty);
        assert_eq!(pointer.byte_width(), 8);
        assert_eq!(
            value(
                &state,
                crate::kernel::program_expression::load(
                    crate::kernel::program_expression::variable("p")
                )
            ),
            expected
        );
        let slot = value(&state, crate::kernel::program_expression::addr_of("p"));
        assert_eq!(slot.program_type(), slot_ty);
        assert_eq!(
            value(
                &state,
                crate::kernel::program_expression::typed_load(
                    ProgramExpression::Value(slot),
                    pointer_ty
                )
            ),
            pointer
        );
        assert_eq!(pointer_ty.pointer_to(), Some(slot_ty));
        assert_eq!(slot_ty.pointer_to(), None);
        assert_eq!(ty.pointer_to(), Some(pointer_ty));
        assert_eq!(ty.abi_alignment(), 16);
        assert_eq!(pointer_ty.abi_alignment(), 8);
        assert_eq!(slot_ty.abi_alignment(), 8);
        let other = if ty == ProgramType::Int128 {
            ProgramType::UInt128Pointer
        } else {
            ProgramType::Int128Pointer
        };
        assert!(!other.accepts(&pointer));
        assert!(ProgramType::VoidPointer.accepts(&pointer));
        assert_eq!(
            ProgramType::function_pointer_signature(ty, &[pointer_ty]),
            CallbackSignature::UNSPECIFIED
        );
    }
}

#[test]
fn wide_address_arrays_use_sixteen_byte_stride_and_preserve_endpoint_values() {
    for (array_ty, ty, literal) in [
        (
            ProgramType::Int128Array(3),
            ProgramType::Int128,
            crate::kernel::program_expression::int128_literal(i128::MIN),
        ),
        (
            ProgramType::UInt128Array(3),
            ProgramType::UInt128,
            crate::kernel::program_expression::uint128_literal(u128::MAX),
        ),
    ] {
        let state = normal(ExecutionState::new(), program_declare("items", array_ty));
        let expected = value(&ExecutionState::new(), literal.clone());
        let base = value(&state, crate::kernel::program_expression::variable("items"));
        assert_eq!(base.program_type(), ty.pointer_to().unwrap());
        let ProgramValue::Pointer(base) = base else {
            unreachable!()
        };
        assert_eq!(
            state.memory.block_size(&base.block).unwrap().as_const(),
            Some(48)
        );
        assert_eq!(array_ty.abi_alignment(), 16);
        let state = normal(state, program_typed_store(element_address(2), literal, ty));
        let last = value(&state, element_address(2));
        let ProgramValue::Pointer(last) = last else {
            unreachable!()
        };
        assert_eq!(last.offset, PointerOffsetTerm::Constant(32));
        assert_eq!(
            value(
                &state,
                crate::kernel::program_expression::index(
                    crate::kernel::program_expression::variable("items"),
                    crate::kernel::program_expression::int32_literal(2)
                )
            ),
            expected
        );
        assert!(matches!(
            outcome(
                &state,
                crate::kernel::program_expression::index(
                    crate::kernel::program_expression::variable("items"),
                    crate::kernel::program_expression::int32_literal(1)
                )
            ),
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
        ));
        // Forming the one-past pointer is valid; dereferencing it is not.
        let past = value(
            &state,
            crate::kernel::program_expression::add(
                crate::kernel::program_expression::variable("items"),
                crate::kernel::program_expression::int32_literal(3),
            ),
        );
        let ProgramValue::Pointer(past) = past else {
            unreachable!()
        };
        assert_eq!(past.offset, PointerOffsetTerm::Constant(48));
        let read_past = crate::kernel::program_expression::typed_load(
            ProgramExpression::Value(ProgramValue::Pointer(past)),
            ty,
        );
        let paths = evaluate_program_expression_paths(
            &state,
            &read_past,
            &PureFactContext::new(),
            &mut ExecutionBudget::for_program_expression(&read_past),
        )
        .unwrap();
        assert!(
            !paths
                .iter()
                .any(|path| matches!(path.outcome, ExpressionOutcome::Value(_))
                    && path.obligations.is_empty())
        );
        assert!(prove_program_expression_evaluation(state, read_past).is_none());
    }
}

#[test]
fn wide_address_pointer_arrays_scale_slots_by_eight_and_pointees_by_sixteen() {
    for (element, pointer_ty, ty, literal) in [
        (
            PointerArrayElement::Int128,
            ProgramType::Int128Pointer,
            ProgramType::Int128,
            crate::kernel::program_expression::int128_literal(i128::MAX),
        ),
        (
            PointerArrayElement::UInt128,
            ProgramType::UInt128Pointer,
            ProgramType::UInt128,
            crate::kernel::program_expression::uint128_literal(1u128 << 100),
        ),
    ] {
        let state = normal(
            ExecutionState::new(),
            program_seq(
                program_declare("wide", ty),
                program_seq(
                    program_assign("wide", literal.clone()),
                    program_declare("items", ProgramType::PointerArray(element, 2)),
                ),
            ),
        );
        let state = normal(
            state,
            program_typed_store(
                element_address(1),
                crate::kernel::program_expression::addr_of("wide"),
                pointer_ty,
            ),
        );
        let ProgramValue::Pointer(slot) = value(&state, element_address(1)) else {
            unreachable!()
        };
        assert_eq!(slot.program_type(), pointer_ty.pointer_to().unwrap());
        assert_eq!(slot.offset, PointerOffsetTerm::Constant(8));
        assert_eq!(
            value(
                &state,
                crate::kernel::program_expression::load(crate::kernel::program_expression::index(
                    crate::kernel::program_expression::variable("items"),
                    crate::kernel::program_expression::int32_literal(1)
                ))
            ),
            value(&ExecutionState::new(), literal)
        );
        assert_eq!(
            PointerArrayElement::from_pointer_type(pointer_ty),
            Some(element)
        );
        assert_eq!(element.pointer_type(), pointer_ty);
        assert_eq!(ProgramType::PointerArray(element, 2).byte_width(), 16);
    }
}

#[test]
fn wide_address_pointer_slot_read_needs_eight_bytes_but_pointee_read_needs_sixteen() {
    let slot = Pointer {
        block: "wide-slot-external".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointee = Pointer {
        block: "wide-pointee-external".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new()
        .with_block(slot.block.clone(), 8)
        .with_block(pointee.block.clone(), 16)
        .store(
            slot.clone(),
            ProgramValue::typed_pointer(pointee.clone(), ProgramType::UInt128Pointer),
        )
        .store(
            pointee.clone(),
            value(
                &ExecutionState::new(),
                crate::kernel::program_expression::uint128_literal(u128::MAX),
            ),
        );
    for bytes in [8, 16] {
        let range = |p| MemoryRange::new_with_element_width(p, 0u32.into(), 1u32.into(), bytes);
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context(ResourceContext::new().unchecked_with_facts([
                ResourceFact::view_memory(MemoryRange::new_with_element_width(
                    slot.clone(),
                    0u32.into(),
                    1u32.into(),
                    8,
                )),
                ResourceFact::view_memory(range(pointee.clone())),
            ]));
        let pointer = value(
            &state,
            crate::kernel::program_expression::typed_load(
                crate::kernel::program_expression::typed_pointer_value(
                    slot.clone(),
                    ProgramType::UInt128PointerPointer,
                ),
                ProgramType::UInt128Pointer,
            ),
        );
        assert_eq!(pointer.program_type(), ProgramType::UInt128Pointer);
        let read = outcome(
            &state,
            crate::kernel::program_expression::typed_load(
                ProgramExpression::Value(pointer),
                ProgramType::UInt128,
            ),
        );
        assert_eq!(matches!(read, ExpressionOutcome::Value(_)), bytes == 16);
        if bytes == 8 {
            assert!(matches!(
                read,
                ExpressionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
            ));
        }
    }
}

#[test]
fn wide_address_symbolic_pointer_slot_reads_keep_eight_byte_access_identity() {
    for pointer_ty in [ProgramType::Int128Pointer, ProgramType::UInt128Pointer] {
        let slot = Pointer {
            block: "wide-symbolic-slot".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        for bytes in [7, 8] {
            let state = ExecutionState::new()
                .with_memory(Memory::new().with_block(slot.block.clone(), 8))
                .with_resource_context(ResourceContext::new().unchecked_with_facts([
                    ResourceFact::view_memory(MemoryRange::new_with_element_width(
                        slot.clone(),
                        0u32.into(),
                        bytes.into(),
                        1,
                    )),
                ]));
            let expression = crate::kernel::program_expression::typed_load(
                crate::kernel::program_expression::typed_pointer_value(
                    slot.clone(),
                    pointer_ty.pointer_to().unwrap(),
                ),
                pointer_ty,
            );
            let first = outcome(&state, expression.clone());
            assert_eq!(first, outcome(&state, expression));
            if bytes == 7 {
                assert!(matches!(
                    first,
                    ExpressionOutcome::RuntimeError(RuntimeError::MissingResource { .. })
                ));
            } else {
                let ExpressionOutcome::Value(pointer) = first else {
                    panic!("pointer read")
                };
                assert_eq!(pointer.program_type(), pointer_ty);
                assert_eq!(pointer.byte_width(), 8);
                assert_eq!(pointer_ty.pointee_type().unwrap().byte_width(), 16);
            }
        }
    }
}

#[test]
fn wide_address_static_array_startup_and_entry_keep_initializer_authority_separate() {
    for (ty, zero_literal, endpoint_literal) in [
        (
            ProgramType::Int128,
            crate::kernel::program_expression::int128_literal(0),
            crate::kernel::program_expression::int128_literal(i128::MIN),
        ),
        (
            ProgramType::UInt128,
            crate::kernel::program_expression::uint128_literal(0),
            crate::kernel::program_expression::uint128_literal(u128::MAX),
        ),
    ] {
        let zero = value(&ExecutionState::new(), zero_literal);
        let endpoint = value(&ExecutionState::new(), endpoint_literal);
        let function = program_function(
            ProgramType::Int32,
            "wide_static",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        )
        .with_static_arrays(vec![StaticArray::new(
            "items",
            "items",
            ty,
            3,
            ArrayContents::new(3, zero.clone(), [(2, endpoint.clone())]),
        )]);
        let at =
            |index: u32| Memory::static_pointer("wide_static", "items").offset_by_bytes(index * 16);
        let startup =
            crate::kernel::initialize_program_program_storage([function.clone()]).unwrap();
        assert_eq!(startup.memory.known_value(&at(0)), Some(zero));
        assert_eq!(startup.memory.known_value(&at(2)), Some(endpoint.clone()));
        assert_eq!(
            value(
                &startup,
                crate::kernel::program_expression::typed_load(
                    crate::kernel::program_expression::typed_pointer_value(
                        at(2),
                        ty.pointer_to().unwrap()
                    ),
                    ty
                )
            ),
            endpoint.clone()
        );
        let entry = initialize_program_function_globals(&ExecutionState::new(), &function);
        assert_ne!(entry.memory.known_value(&at(2)), Some(endpoint.clone()));
        assert!(entry.resources.facts().is_empty());
        // Nested entry retains a caller's writes; it cannot restore an initializer.
        let changed = startup.with_memory(entry.memory.clone().store(at(2), endpoint.clone()));
        let nested = initialize_program_function_globals(&changed, &function);
        assert_eq!(nested.memory.known_value(&at(2)), Some(endpoint));
    }
}

#[test]
fn wide_address_narrow_array_copy_refuses_a_wide_cell_overlapping_its_prefix() {
    let at = |offset| Pointer {
        block: "local:wide-prefix".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let mut memory = Memory::new()
        .with_block("local:wide-prefix", 16)
        .with_block("local:wide-target", 8)
        .with_initialized_object(&at(0), 16)
        .store(
            at(0),
            value(
                &ExecutionState::new(),
                crate::kernel::program_expression::uint128_literal(u128::MAX),
            ),
        );
    for offset in 8..16 {
        memory = memory.store(at(offset), uint8(1));
    }
    // Compact copies require a homogeneous source region. Its indexed prefix check
    // must see the wide cell starting eight bytes before this byte region.
    assert!(
        memory
            .write_scalar_array_region(
                &Pointer {
                    block: "local:wide-target".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramType::UInt8,
                8,
                ProgramValue::typed_pointer(at(8), ProgramType::UInt8Pointer),
                true,
                false,
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn checked_object_address_accepts_uninitialized_storage_without_reading_it() {
    let state = normal(
        ExecutionState::new(),
        program_declare("items", ProgramType::Int32Array(2)),
    );
    let pointer = crate::kernel::program_expression::checked_object_address(
        crate::kernel::program_expression::index(
            crate::kernel::program_expression::variable("items"),
            crate::kernel::program_expression::int32_literal(1),
        ),
    );
    let address = value(&state, pointer);
    assert_eq!(address, value(&state, element_address(1)));
    assert!(matches!(
        outcome(
            &state,
            crate::kernel::program_expression::typed_load(
                ProgramExpression::Value(address),
                ProgramType::Int32
            )
        ),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
    ));
}

#[test]
fn checked_object_address_rejects_one_past_while_c_address_cancellation_preserves_it() {
    let state = normal(
        ExecutionState::new(),
        program_declare("items", ProgramType::Int32Array(2)),
    );
    assert!(matches!(
        outcome(&state, element_address(2)),
        ExpressionOutcome::Value(ProgramValue::Pointer(_))
    ));
    assert!(matches!(
        outcome(
            &state,
            crate::kernel::program_expression::checked_object_address(
                crate::kernel::program_expression::index(
                    crate::kernel::program_expression::variable("items"),
                    crate::kernel::program_expression::int32_literal(2)
                )
            )
        ),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
    ));
    assert!(matches!(
        outcome(
            &state,
            crate::kernel::program_expression::checked_object_address(
                crate::kernel::program_expression::typed_load(
                    ProgramExpression::Value(ProgramValue::typed_pointer(
                        Pointer::null(),
                        ProgramType::Int32Pointer
                    )),
                    ProgramType::Int32
                )
            )
        ),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn checked_object_address_rejects_storage_after_its_local_lifetime_ends() {
    let state = normal(
        ExecutionState::new(),
        program_declare("items", ProgramType::Int32Array(2)),
    );
    let address = value(&state, element_address(0));
    let ProgramValue::Pointer(pointer) = &address else {
        unreachable!()
    };
    let retired = state
        .clone()
        .with_memory(state.memory().without_local_block(&pointer.pointer().block));
    assert!(matches!(
        outcome(
            &retired,
            crate::kernel::program_expression::checked_object_address(
                crate::kernel::program_expression::typed_load(
                    ProgramExpression::Value(address),
                    ProgramType::Int32
                )
            )
        ),
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
    ));
}

#[test]
fn wide_pointer_subtraction_preserves_unsigned_magnitude_and_bounds() {
    let state = ExecutionState::new().with_memory(Memory::new().with_block("offsets", 16));
    let at = |offset| Pointer {
        block: "offsets".into(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    for ty in [
        ProgramType::VoidPointer,
        ProgramType::UInt8Pointer,
        ProgramType::Int32Pointer,
    ] {
        let stride = if ty == ProgramType::Int32Pointer {
            4
        } else {
            1
        };
        for offset in [
            crate::kernel::program_expression::uint32_literal(1),
            crate::kernel::program_expression::uint64_literal(1),
            crate::kernel::program_expression::int64_literal(1),
        ] {
            let result = value(
                &state,
                crate::kernel::program_expression::subtract(
                    crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::typed_pointer_value(at(8), ty),
                        ty,
                    ),
                    offset,
                ),
            );
            assert_eq!(result, ProgramValue::typed_pointer(at(8 - stride), ty));
        }
        let result = value(
            &state,
            crate::kernel::program_expression::subtract(
                crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::typed_pointer_value(at(8), ty),
                    ty,
                ),
                crate::kernel::program_expression::int64_literal(-1),
            ),
        );
        assert_eq!(result, ProgramValue::typed_pointer(at(8 + stride), ty));
        for offset in [
            crate::kernel::program_expression::uint64_literal(17),
            crate::kernel::program_expression::uint64_literal(u64::MAX),
            crate::kernel::program_expression::int64_literal(i64::MIN),
        ] {
            assert!(matches!(
                outcome(
                    &state,
                    crate::kernel::program_expression::subtract(
                        crate::kernel::program_expression::cast(
                            crate::kernel::program_expression::typed_pointer_value(at(8), ty),
                            ty
                        ),
                        offset
                    )
                ),
                ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic)
            ));
        }
        for offset in [
            crate::kernel::program_expression::uint32_literal(0),
            crate::kernel::program_expression::uint64_literal(0),
            crate::kernel::program_expression::int64_literal(0),
        ] {
            assert_eq!(
                value(
                    &state,
                    crate::kernel::program_expression::subtract(
                        crate::kernel::program_expression::cast(
                            crate::kernel::program_expression::typed_pointer_value(at(0), ty),
                            ty
                        ),
                        offset
                    )
                ),
                ProgramValue::typed_pointer(at(0), ty)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/wide_address_tests.rs");
}
