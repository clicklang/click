//! The little-endian byte view of integer cells: one-byte C loads and stores
//! inside a wider integer cell, and every case that must stay refused.

use super::*;
use crate::kernel::eval::{ContainingIntegerCell, containing_integer_cell, integer_cell_byte};

fn word(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:word"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn load_byte(
    memory: &CMemory,
    offset: i64,
    value_type: CType,
    byte_order: Option<ByteOrder>,
) -> CExpressionOutcome {
    let paths = evaluate_c_memory_load_paths(
        memory,
        word(offset),
        value_type,
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
        false,
        false,
        None,
        byte_order,
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    paths[0].outcome.clone()
}

fn store_byte(memory: CMemory, offset: i64, byte: CValue, byte_order: ByteOrder) -> CMemory {
    let state = CState::new().with_memory(memory.clone());
    let state = if memory.requires_explicit_scalar_ownership(&word(0)) {
        state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                word(0),
                0.into(),
                memory.block_size(&word(0).block).unwrap().clone(),
                1,
            )),
        ))
    } else {
        state
    };
    let value_type = if matches!(byte, CValue::Int8(_)) {
        CType::Int8
    } else {
        CType::UInt8
    };
    let statement = CStatement::TypedStore {
        access_class: None,
        pointer: CExpression::Value(CValue::typed_pointer(
            word(offset),
            if value_type == CType::Int8 {
                CType::Int8Pointer
            } else {
                CType::UInt8Pointer
            },
        )),
        value: CExpression::Value(byte),
        value_type,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        CExecutionContext::execute_bodies(
            &CExecutionEnvironment::new().with_byte_order(byte_order),
        ),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let CStatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("byte store should execute: {:?}", paths[0].outcome);
    };
    state.memory().clone()
}

fn uint8_constant(value: u32) -> CExpressionOutcome {
    CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(value)))
}

#[test]
fn byte_stores_complete_declared_uint32_and_preserve_byte_observations() {
    let mut memory = CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32);
    // Out-of-order stores must not treat a partial representation as a word.
    for (offset, byte) in [(3, 0xFF), (1, 0x80), (0, 0x11)] {
        memory = store_byte(
            memory,
            offset,
            CValue::UInt8(byte.into()),
            ByteOrder::Little,
        );
        assert!(!matches!(
            memory.known_value(&word(0)),
            Some(CValue::UInt32(_))
        ));
    }
    memory = store_byte(
        memory,
        2,
        CValue::Int8(0xFFFF_FFEEu32.into()),
        ByteOrder::Little,
    );
    assert_eq!(
        memory.known_value(&word(0)),
        Some(CValue::UInt32(0xFFEE_8011u32.into()))
    );
    assert_eq!(memory.cells.len(), 1);
    for (offset, byte) in [(0, 0x11), (1, 0x80), (2, 0xEE), (3, 0xFF)] {
        assert_eq!(
            load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(byte)
        );
    }
    memory = store_byte(memory, 1, CValue::UInt8(7u32.into()), ByteOrder::Little);
    assert_eq!(
        memory.known_value(&word(0)),
        Some(CValue::UInt32(0xFFEE_0711u32.into()))
    );
}

#[test]
fn byte_assembly_refuses_untyped_other_types_missing_bytes_and_other_orders() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let prefix = |mut memory: CMemory| {
        for byte in 0..3 {
            memory = memory.store(word(byte), CValue::UInt8(1u32.into()));
        }
        memory
    };
    let typed = prefix(CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32));
    let incoming = CValue::UInt8(2u32.into());
    assert!(assemble(&typed, &word(3), &incoming, Some(ByteOrder::Little)).is_some());
    for order in [None, Some(ByteOrder::Big)] {
        assert!(assemble(&typed, &word(3), &incoming, order).is_none());
    }
    for memory in [
        prefix(CMemory::new().with_block(word(0).block, 4)),
        prefix(CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::Int32)),
        prefix(CMemory::new().with_declared_scalar_block(word(0).block, 8, CType::UInt64)),
        CMemory::new()
            .with_declared_scalar_block(word(0).block, 4, CType::UInt32)
            .store(word(0), CValue::UInt8(1u32.into())),
        typed.without_local_block(&word(0).block),
    ] {
        assert!(assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little)).is_none());
    }
    assert!(assemble(&typed, &word(4), &incoming, Some(ByteOrder::Little)).is_none());
    assert!(
        assemble(
            &typed,
            &word(3),
            &CValue::UInt32(2u32.into()),
            Some(ByteOrder::Little)
        )
        .is_none()
    );
}

/// Whether a load produced a constant byte, which only the byte view (or an
/// exact one-byte cell) can do in these memories.
fn is_constant_byte(outcome: &CExpressionOutcome) -> bool {
    matches!(
        outcome,
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(_)))
    )
}

fn is_load_type_mismatch(outcome: &CExpressionOutcome) -> bool {
    matches!(
        outcome,
        CExpressionOutcome::RuntimeError(CRuntimeError::LoadTypeMismatch { .. })
    )
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_a_constant_uint32_cell() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
    for (offset, expected) in [(0, 0x11), (1, 0x22), (2, 0x33), (3, 0x44)] {
        assert_eq!(
            load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(expected),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_constant_64_bit_cells() {
    let bits = 0x8877_6655_4433_2211_u64;
    for cell in [
        CValue::UInt64(Bitvector32Term::UInt64Constant(bits)),
        CValue::Int64(Bitvector32Term::Int64Constant(bits as i64)),
    ] {
        let memory = CMemory::new().store(word(0), cell.clone());
        for offset in 0..8 {
            assert_eq!(
                load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little)),
                uint8_constant(((bits >> (8 * offset)) & 0xFF) as u32),
                "{cell:?} byte {offset}"
            );
        }
    }
}

#[test]
fn byte_loads_of_symbolic_cells_extract_the_shifted_masked_byte() {
    let value = Bitvector32Term::Variable(Variable(7301));
    let memory = CMemory::new().store(word(0), CValue::UInt32(value.clone()));
    assert_eq!(
        load_byte(&memory, 2, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::BitwiseAnd(
            Box::new(Bitvector32Term::LogicalShiftRight(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(16)),
            )),
            Box::new(Bitvector32Term::Constant(0xFF)),
        )))
    );

    let wide = Bitvector32Term::Variable(Variable(7302));
    let memory = CMemory::new().store(word(0), CValue::UInt64(wide.clone()));
    assert_eq!(
        load_byte(&memory, 5, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::UInt32From64(Box::new(
            Bitvector32Term::UInt64BitwiseAnd(
                Box::new(Bitvector32Term::UInt64LogicalShiftRight(
                    Box::new(wide),
                    Box::new(Bitvector32Term::UInt64Constant(40)),
                )),
                Box::new(Bitvector32Term::UInt64Constant(0xFF)),
            )
        ))))
    );

    // The same extraction folds to the byte once the value is known.
    let cell = ContainingIntegerCell {
        pointer: word(0),
        value: CValue::UInt32(0xA1B2_C3D4.into()),
        byte: 1,
    };
    assert_eq!(
        integer_cell_byte(&cell.value, cell.byte),
        Some(Bitvector32Term::Constant(0xC3))
    );
}

#[test]
fn signed_byte_loads_sign_extend_a_constant_byte_and_refuse_a_symbolic_one() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x0000_7F80.into()));
    assert_eq!(
        load_byte(&memory, 0, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(0xFFFF_FF80)))
    );
    assert_eq!(
        load_byte(&memory, 1, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(0x7F)))
    );
    let symbolic = CMemory::new().store(
        word(0),
        CValue::UInt32(Bitvector32Term::Variable(Variable(7303))),
    );
    assert!(is_load_type_mismatch(&load_byte(
        &symbolic,
        1,
        CType::Int8,
        Some(ByteOrder::Little)
    )));
}

#[test]
fn byte_stores_update_the_containing_uint32_cell_in_place() {
    for (offset, expected) in [
        (0, 0x4433_22AB_u32),
        (1, 0x4433_AB11),
        (2, 0x44AB_2211),
        (3, 0xAB33_2211),
    ] {
        let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
        let after = store_byte(
            memory,
            offset,
            CValue::UInt8(0xAB.into()),
            ByteOrder::Little,
        );
        assert_eq!(
            after.known_value(&word(0)),
            Some(CValue::UInt32(Bitvector32Term::Constant(expected))),
            "byte {offset}"
        );
        // The updated cell is the only description of this storage.
        for other in 1..4 {
            assert_eq!(after.known_value(&word(other)), None, "byte {offset}");
        }
        assert_eq!(
            load_byte(&after, offset, CType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(0xAB)
        );
    }
}

#[test]
fn byte_stores_update_the_containing_uint64_cell_in_place() {
    let bits = 0x8877_6655_4433_2211_u64;
    for offset in 0..8 {
        let memory = CMemory::new().store(
            word(0),
            CValue::UInt64(Bitvector32Term::UInt64Constant(bits)),
        );
        let after = store_byte(memory, offset, CValue::UInt8(0.into()), ByteOrder::Little);
        assert_eq!(
            after.known_value(&word(0)),
            Some(CValue::UInt64(Bitvector32Term::UInt64Constant(
                bits & !(0xFF << (8 * offset))
            ))),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_stores_into_a_symbolic_uint32_cell_keep_the_other_bytes() {
    let value = Bitvector32Term::Variable(Variable(7304));
    let memory = CMemory::new().store(word(0), CValue::UInt32(value.clone()));
    let after = store_byte(memory, 1, CValue::UInt8(0x5A.into()), ByteOrder::Little);
    assert_eq!(
        after.known_value(&word(0)),
        Some(CValue::UInt32(Bitvector32Term::BitwiseOr(
            Box::new(Bitvector32Term::BitwiseAnd(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(0xFFFF_00FF)),
            )),
            Box::new(Bitvector32Term::Constant(0x5A00)),
        )))
    );
}

#[test]
fn big_endian_and_uninstalled_byte_orders_have_no_byte_view() {
    let memory = CMemory::new().store(word(0), CValue::UInt32(0x4433_2211.into()));
    for byte_order in [Some(ByteOrder::Big), None] {
        assert!(is_load_type_mismatch(&load_byte(
            &memory,
            0,
            CType::UInt8,
            byte_order
        )));
        assert!(
            !is_constant_byte(&load_byte(&memory, 1, CType::UInt8, byte_order)),
            "{byte_order:?}"
        );
        assert_eq!(containing_integer_cell(&memory, &word(1), byte_order), None);
    }
    // A big-endian store keeps today's behavior: the wider cell is forgotten.
    let after = store_byte(memory, 1, CValue::UInt8(0xAB.into()), ByteOrder::Big);
    assert_eq!(after.known_value(&word(0)), None);
    assert_eq!(
        after.known_value(&word(1)),
        Some(CValue::UInt8(Bitvector32Term::Constant(0xAB)))
    );
}

#[test]
fn pointer_cells_have_no_byte_view() {
    let target = Pointer {
        block: PointerBlock::from("global:target"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(word(0), CValue::typed_pointer(target, CType::Int32Pointer));
    for offset in [0, 1, 7] {
        assert_eq!(
            containing_integer_cell(&memory, &word(offset), Some(ByteOrder::Little)),
            None
        );
        let outcome = load_byte(&memory, offset, CType::UInt8, Some(ByteOrder::Little));
        assert!(!is_constant_byte(&outcome), "byte {offset}: {outcome:?}");
        if offset == 0 {
            assert!(is_load_type_mismatch(&outcome), "{outcome:?}");
        }
    }
    let after = store_byte(memory, 1, CValue::UInt8(0.into()), ByteOrder::Little);
    assert_eq!(after.known_value(&word(0)), None);
}

#[test]
fn a_one_byte_cell_is_read_as_its_own_access() {
    let memory = CMemory::new().store(word(1), CValue::UInt8(9.into()));
    assert_eq!(
        containing_integer_cell(&memory, &word(1), Some(ByteOrder::Little)),
        None
    );
    assert_eq!(
        load_byte(&memory, 1, CType::UInt8, Some(ByteOrder::Little)),
        uint8_constant(9)
    );
}

/// C11 6.5p7: a character load of a one-byte cell of the other signedness
/// reads the same eight bits. Constants fold to the reinterpreted value in
/// both directions; a symbolic cell keeps an explicit modular conversion of
/// its own term, never a fresh unrelated value.
#[test]
fn character_loads_read_a_one_byte_cell_of_the_other_signedness_as_its_bits() {
    let int8 = |value: i8| CValue::Int8(Bitvector32Term::Constant(value as i32 as u32));
    let uint8 = |value: u8| CValue::UInt8(Bitvector32Term::Constant(u32::from(value)));
    for byte in [0u8, 1, 0x7F, 0x80, 0xC8, 0xFF] {
        assert_eq!(CType::UInt8.read_cell(&int8(byte as i8)), Some(uint8(byte)));
        assert_eq!(CType::Int8.read_cell(&uint8(byte)), Some(int8(byte as i8)));
        assert_eq!(
            CType::Int8.read_cell(&int8(byte as i8)),
            Some(int8(byte as i8))
        );
        assert_eq!(
            LoadKind::UInt8.read_cell(&int8(byte as i8)),
            Some(uint8(byte))
        );
        assert_eq!(
            LoadKind::Int8.read_cell(&uint8(byte)),
            Some(int8(byte as i8))
        );
    }
    let variable = Bitvector32Term::Variable(Variable(613_001));
    assert_eq!(
        CType::UInt8.read_cell(&CValue::Int8(variable.clone())),
        Some(CValue::UInt8(Bitvector32Term::machine_integer_cast(
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            variable.clone(),
        )))
    );
    // Reading back through the original signedness is the original term.
    let Some(CValue::Int8(round_trip)) = CType::UInt8
        .read_cell(&CValue::Int8(variable.clone()))
        .and_then(|value| CType::Int8.read_cell(&value))
    else {
        panic!("a character round trip reads a signed byte");
    };
    assert_eq!(round_trip, variable);
    // No other cell gains a character view: wider integers go through the
    // byte view, and bool, pointer, and float cells stay refused. A wider
    // load reads only a cell of its own width.
    for (load, stored) in [
        (CType::UInt8, CValue::Int16(Bitvector32Term::Constant(1))),
        (CType::Int8, CValue::Bool(Bitvector32Term::Constant(1))),
        (CType::UInt8, CValue::Float32(Bitvector32Term::Constant(0))),
        (CType::Int16, CValue::UInt8(Bitvector32Term::Constant(1))),
        (CType::Int32, CValue::Int16(Bitvector32Term::Constant(1))),
        (CType::UInt64, CValue::UInt32(Bitvector32Term::Constant(1))),
        (CType::UInt16, CValue::Int8(Bitvector32Term::Constant(1))),
    ] {
        assert_eq!(load.read_cell(&stored), None, "{load:?} of {stored:?}");
    }
}

/// C11 6.5p7 and GCC's `-Wpointer-sign`: a 16-, 32-, or 64-bit load of a
/// cell of the same width and the other signedness reads the same bits.
/// Constants fold in both directions; a symbolic 16-bit cell keeps an
/// explicit modular conversion, a 32-bit word is the same term under the
/// other tag, and a 64-bit word uses the bit-preserving carrier conversion.
#[test]
fn integer_loads_read_a_cell_of_the_other_signedness_as_its_bits() {
    let int16 = |value: i16| CValue::Int16(Bitvector32Term::Constant(value as i32 as u32));
    let uint16 = |value: u16| CValue::UInt16(Bitvector32Term::Constant(u32::from(value)));
    for half in [0u16, 1, 0x7FFF, 0x8000, 0xFFC8, 0xFFFF] {
        assert_eq!(
            CType::UInt16.read_cell(&int16(half as i16)),
            Some(uint16(half))
        );
        assert_eq!(
            CType::Int16.read_cell(&uint16(half)),
            Some(int16(half as i16))
        );
        assert_eq!(
            LoadKind::UInt16.read_cell(&int16(half as i16)),
            Some(uint16(half))
        );
        assert_eq!(
            LoadKind::Int16.read_cell(&uint16(half)),
            Some(int16(half as i16))
        );
    }
    for word in [0u32, 1, 0x7FFF_FFFF, 0x8000_0000, 0xFFFF_FFFF] {
        let bits = Bitvector32Term::Constant(word);
        assert_eq!(
            CType::UInt32.read_cell(&CValue::Int32(bits.clone())),
            Some(CValue::UInt32(bits.clone()))
        );
        assert_eq!(
            CType::Int32.read_cell(&CValue::UInt32(bits.clone())),
            Some(CValue::Int32(bits))
        );
    }
    for word in [
        0u64,
        1,
        0x7FFF_FFFF_FFFF_FFFF,
        0x8000_0000_0000_0000,
        u64::MAX,
    ] {
        assert_eq!(
            CType::UInt64.read_cell(&CValue::Int64(Bitvector32Term::Int64Constant(word as i64))),
            Some(CValue::UInt64(Bitvector32Term::UInt64Constant(word)))
        );
        assert_eq!(
            CType::Int64.read_cell(&CValue::UInt64(Bitvector32Term::UInt64Constant(word))),
            Some(CValue::Int64(Bitvector32Term::Int64Constant(word as i64)))
        );
    }
    let variable = Bitvector32Term::Variable(Variable(613_002));
    assert_eq!(
        CType::UInt16.read_cell(&CValue::Int16(variable.clone())),
        Some(CValue::UInt16(Bitvector32Term::machine_integer_cast(
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            variable.clone(),
        )))
    );
    let Some(CValue::Int16(round_trip)) = CType::UInt16
        .read_cell(&CValue::Int16(variable.clone()))
        .and_then(|value| CType::Int16.read_cell(&value))
    else {
        panic!("a halfword round trip reads a signed halfword");
    };
    assert_eq!(round_trip, variable);
    let Some(CValue::Int64(round_trip)) = CType::UInt64
        .read_cell(&CValue::Int64(variable.clone()))
        .and_then(|value| CType::Int64.read_cell(&value))
    else {
        panic!("a 64-bit round trip reads a signed word");
    };
    assert_eq!(round_trip, variable);
}

/// The execution load path applies the rule: a cell stored as `signed char`
/// is read through `unsigned char` as its bits, and the reverse.
#[test]
fn execution_loads_read_character_cells_of_the_other_signedness() {
    let memory = CMemory::new()
        .store(
            word(0),
            CValue::Int8(Bitvector32Term::Constant(-56i32 as u32)),
        )
        .store(word(1), CValue::UInt8(Bitvector32Term::Constant(200)));
    assert_eq!(
        load_byte(&memory, 0, CType::UInt8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::UInt8(Bitvector32Term::Constant(200)))
    );
    assert_eq!(
        load_byte(&memory, 1, CType::Int8, Some(ByteOrder::Little)),
        CExpressionOutcome::Value(CValue::Int8(Bitvector32Term::Constant(-56i32 as u32)))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/byte_view_tests.rs");
}
