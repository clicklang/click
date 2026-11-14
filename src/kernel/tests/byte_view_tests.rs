//! The little-endian byte view of integer cells: one-byte C loads and stores
//! inside a wider integer cell, and every case that must stay refused.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::eval::{ContainingIntegerCell, containing_integer_cell, integer_cell_byte};
use crate::kernel::{int32_constant, native_constant};

fn word(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:word"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn load_byte(
    memory: &Memory,
    offset: i64,
    value_type: ProgramType,
    byte_order: Option<ByteOrder>,
) -> ExpressionOutcome {
    let paths = evaluate_memory_load_paths(
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

fn store_byte(memory: Memory, offset: i64, byte: ProgramValue, byte_order: ByteOrder) -> Memory {
    let state = ExecutionState::new().with_memory(memory.clone());
    let state = if memory.requires_explicit_scalar_ownership(&word(0)) {
        state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                word(0),
                0.into(),
                memory.block_size(&word(0).block).unwrap().clone(),
                1,
            )),
        ))
    } else {
        state
    };
    let value_type = if matches!(byte, ProgramValue::Int8(_)) {
        ProgramType::Int8
    } else {
        ProgramType::UInt8
    };
    let statement = ProgramStatement::TypedStore {
        access_class: None,
        pointer: ProgramExpression::Value(ProgramValue::typed_pointer(
            word(offset),
            if value_type == ProgramType::Int8 {
                ProgramType::Int8Pointer
            } else {
                ProgramType::UInt8Pointer
            },
        )),
        value: ProgramExpression::Value(byte),
        value_type,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let paths = execute_execution_statement_paths(
        &state,
        &statement,
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new().with_byte_order(byte_order)),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let StatementOutcome::Normal(state) = &paths[0].outcome else {
        panic!("byte store should execute: {:?}", paths[0].outcome);
    };
    state.memory().clone()
}

fn uint8_constant(value: u32) -> ExpressionOutcome {
    ExpressionOutcome::Value(crate::kernel::uint8(value))
}

#[test]
fn byte_stores_complete_declared_uint32_and_preserve_byte_observations() {
    let mut memory =
        Memory::new().with_declared_scalar_block(word(0).block, 4, ProgramType::UInt32);
    // Out-of-order stores must not treat a partial representation as a word.
    for (offset, byte) in [(3, 0xFF), (1, 0x80), (0, 0x11)] {
        memory = store_byte(
            memory,
            offset,
            crate::kernel::uint8(byte),
            ByteOrder::Little,
        );
        assert!(!matches!(
            memory.known_value(&word(0)),
            Some(ProgramValue::UInt32(_))
        ));
    }
    memory = store_byte(
        memory,
        2,
        crate::kernel::int8(0xFFFF_FFEEu32),
        ByteOrder::Little,
    );
    assert_eq!(
        memory.known_value(&word(0)),
        Some(ProgramValue::UInt32(0xFFEE_8011u32.into()))
    );
    assert_eq!(memory.cells.len(), 1);
    for (offset, byte) in [(0, 0x11), (1, 0x80), (2, 0xEE), (3, 0xFF)] {
        assert_eq!(
            load_byte(&memory, offset, ProgramType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(byte)
        );
    }
    memory = store_byte(memory, 1, crate::kernel::uint8(7u32), ByteOrder::Little);
    assert_eq!(
        memory.known_value(&word(0)),
        Some(ProgramValue::UInt32(0xFFEE_0711u32.into()))
    );
}

#[test]
fn byte_assembly_refuses_untyped_other_types_missing_bytes_and_other_orders() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let prefix = |mut memory: Memory| {
        for byte in 0..3 {
            memory = memory.store(word(byte), crate::kernel::uint8(1u32));
        }
        memory
    };
    let typed =
        prefix(Memory::new().with_declared_scalar_block(word(0).block, 4, ProgramType::UInt32));
    let incoming = crate::kernel::uint8(2u32);
    assert!(assemble(&typed, &word(3), &incoming, Some(ByteOrder::Little)).is_some());
    for order in [None, Some(ByteOrder::Big)] {
        assert!(assemble(&typed, &word(3), &incoming, order).is_none());
    }
    for memory in [
        prefix(Memory::new().with_block(word(0).block, 4)),
        prefix(Memory::new().with_declared_scalar_block(word(0).block, 4, ProgramType::Int32)),
        prefix(Memory::new().with_declared_scalar_block(word(0).block, 8, ProgramType::UInt64)),
        Memory::new()
            .with_declared_scalar_block(word(0).block, 4, ProgramType::UInt32)
            .store(word(0), crate::kernel::uint8(1u32)),
        typed.without_local_block(&word(0).block),
    ] {
        assert!(assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little)).is_none());
    }
    assert!(assemble(&typed, &word(4), &incoming, Some(ByteOrder::Little)).is_none());
    assert!(
        assemble(
            &typed,
            &word(3),
            &ProgramValue::UInt32(2u32.into()),
            Some(ByteOrder::Little)
        )
        .is_none()
    );
}

/// Whether a load produced a constant byte, which only the byte view (or an
/// exact one-byte cell) can do in these memories.
fn is_constant_byte(outcome: &ExpressionOutcome) -> bool {
    matches!(
        outcome,
        ExpressionOutcome::Value(ProgramValue::UInt8(native_constant!(_, _)))
    )
}

fn is_load_type_mismatch(outcome: &ExpressionOutcome) -> bool {
    matches!(
        outcome,
        ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch { .. })
    )
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_a_constant_uint32_cell() {
    let memory = Memory::new().store(word(0), ProgramValue::UInt32(0x4433_2211.into()));
    for (offset, expected) in [(0, 0x11), (1, 0x22), (2, 0x33), (3, 0x44)] {
        assert_eq!(
            load_byte(&memory, offset, ProgramType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(expected),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_loads_read_each_little_endian_byte_of_constant_64_bit_cells() {
    let bits = 0x8877_6655_4433_2211_u64;
    for cell in [
        ProgramValue::UInt64(MachineTerm::uint64_constant(bits)),
        ProgramValue::Int64(MachineTerm::int64_constant(bits as i64)),
    ] {
        let memory = Memory::new().store(word(0), cell.clone());
        for offset in 0..8 {
            assert_eq!(
                load_byte(&memory, offset, ProgramType::UInt8, Some(ByteOrder::Little)),
                uint8_constant(((bits >> (8 * offset)) & 0xFF) as u32),
                "{cell:?} byte {offset}"
            );
        }
    }
}

#[test]
fn byte_loads_of_symbolic_cells_extract_the_shifted_masked_byte() {
    let value = MachineTerm::Variable(Variable(7301));
    let memory = Memory::new().store(word(0), ProgramValue::UInt32(value.clone()));
    assert_eq!(
        load_byte(&memory, 2, ProgramType::UInt8, Some(ByteOrder::Little)),
        // A byte view is the byte's native `uint8` term.
        ExpressionOutcome::Value(ProgramValue::UInt8(MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt32,
            MachineIntegerType::UInt8,
            binary_node!(
                UInt32,
                ShiftRight,
                Box::new(value.clone()),
                Box::new(MachineTerm::uint32_constant(16)),
            ),
        )))
    );

    let wide = MachineTerm::Variable(Variable(7302));
    let memory = Memory::new().store(word(0), ProgramValue::UInt64(wide.clone()));
    assert_eq!(
        load_byte(&memory, 5, ProgramType::UInt8, Some(ByteOrder::Little)),
        ExpressionOutcome::Value(ProgramValue::UInt8(MachineTerm::machine_integer_cast(
            MachineIntegerType::UInt64,
            MachineIntegerType::UInt8,
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftRight,
                left: Box::new(wide),
                right: Box::new(MachineTerm::uint64_constant(40))
            },
        )))
    );

    // The same extraction folds to the byte once the value is known.
    let cell = ContainingIntegerCell {
        pointer: word(0),
        value: ProgramValue::UInt32(0xA1B2_C3D4.into()),
        byte: 1,
    };
    assert_eq!(
        integer_cell_byte(&cell.value, cell.byte),
        Some(MachineTerm::narrow_constant(
            MachineIntegerType::UInt8,
            0xC3
        ))
    );
}

#[test]
fn signed_byte_loads_sign_extend_a_constant_byte_and_refuse_a_symbolic_one() {
    let memory = Memory::new().store(word(0), ProgramValue::UInt32(0x0000_7F80.into()));
    assert_eq!(
        load_byte(&memory, 0, ProgramType::Int8, Some(ByteOrder::Little)),
        ExpressionOutcome::Value(crate::kernel::int8(0xFFFF_FF80))
    );
    assert_eq!(
        load_byte(&memory, 1, ProgramType::Int8, Some(ByteOrder::Little)),
        ExpressionOutcome::Value(crate::kernel::int8(0x7F))
    );
    let symbolic = Memory::new().store(
        word(0),
        ProgramValue::UInt32(MachineTerm::Variable(Variable(7303))),
    );
    assert!(is_load_type_mismatch(&load_byte(
        &symbolic,
        1,
        ProgramType::Int8,
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
        let memory = Memory::new().store(word(0), ProgramValue::UInt32(0x4433_2211.into()));
        let after = store_byte(
            memory,
            offset,
            crate::kernel::uint8(0xABu32),
            ByteOrder::Little,
        );
        assert_eq!(
            after.known_value(&word(0)),
            Some(ProgramValue::UInt32(MachineTerm::constant(expected))),
            "byte {offset}"
        );
        // The updated cell is the only description of this storage.
        for other in 1..4 {
            assert_eq!(after.known_value(&word(other)), None, "byte {offset}");
        }
        assert_eq!(
            load_byte(&after, offset, ProgramType::UInt8, Some(ByteOrder::Little)),
            uint8_constant(0xAB)
        );
    }
}

#[test]
fn byte_stores_update_the_containing_uint64_cell_in_place() {
    let bits = 0x8877_6655_4433_2211_u64;
    for offset in 0..8 {
        let memory = Memory::new().store(
            word(0),
            ProgramValue::UInt64(MachineTerm::uint64_constant(bits)),
        );
        let after = store_byte(memory, offset, crate::kernel::uint8(0), ByteOrder::Little);
        assert_eq!(
            after.known_value(&word(0)),
            Some(ProgramValue::UInt64(MachineTerm::uint64_constant(
                bits & !(0xFF << (8 * offset))
            ))),
            "byte {offset}"
        );
    }
}

#[test]
fn byte_stores_into_a_symbolic_uint32_cell_keep_the_other_bytes() {
    let value = MachineTerm::Variable(Variable(7304));
    let memory = Memory::new().store(word(0), ProgramValue::UInt32(value.clone()));
    let after = store_byte(memory, 1, crate::kernel::uint8(0x5Au32), ByteOrder::Little);
    assert_eq!(
        after.known_value(&word(0)),
        Some(ProgramValue::UInt32(binary_node!(
            Int32,
            BitwiseOr,
            Box::new(binary_node!(
                Int32,
                BitwiseAnd,
                Box::new(value),
                Box::new(MachineTerm::constant(0xFFFF_00FF)),
            )),
            Box::new(MachineTerm::constant(0x5A00)),
        )))
    );
}

#[test]
fn big_endian_and_uninstalled_byte_orders_have_no_byte_view() {
    let memory = Memory::new().store(word(0), ProgramValue::UInt32(0x4433_2211.into()));
    for byte_order in [Some(ByteOrder::Big), None] {
        assert!(is_load_type_mismatch(&load_byte(
            &memory,
            0,
            ProgramType::UInt8,
            byte_order
        )));
        assert!(
            !is_constant_byte(&load_byte(&memory, 1, ProgramType::UInt8, byte_order)),
            "{byte_order:?}"
        );
        assert_eq!(containing_integer_cell(&memory, &word(1), byte_order), None);
    }
    // A big-endian store keeps today's behavior: the wider cell is forgotten.
    let after = store_byte(memory, 1, crate::kernel::uint8(0xABu32), ByteOrder::Big);
    assert_eq!(after.known_value(&word(0)), None);
    assert_eq!(
        after.known_value(&word(1)),
        Some(crate::kernel::uint8(0xAB))
    );
}

#[test]
fn pointer_cells_have_no_byte_view() {
    let target = Pointer {
        block: PointerBlock::from("global:target"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().store(
        word(0),
        ProgramValue::typed_pointer(target, ProgramType::Int32Pointer),
    );
    for offset in [0, 1, 7] {
        assert_eq!(
            containing_integer_cell(&memory, &word(offset), Some(ByteOrder::Little)),
            None
        );
        let outcome = load_byte(&memory, offset, ProgramType::UInt8, Some(ByteOrder::Little));
        assert!(!is_constant_byte(&outcome), "byte {offset}: {outcome:?}");
        if offset == 0 {
            assert!(is_load_type_mismatch(&outcome), "{outcome:?}");
        }
    }
    let after = store_byte(memory, 1, crate::kernel::uint8(0), ByteOrder::Little);
    assert_eq!(after.known_value(&word(0)), None);
}

#[test]
fn a_one_byte_cell_is_read_as_its_own_access() {
    let memory = Memory::new().store(word(1), crate::kernel::uint8(9));
    assert_eq!(
        containing_integer_cell(&memory, &word(1), Some(ByteOrder::Little)),
        None
    );
    assert_eq!(
        load_byte(&memory, 1, ProgramType::UInt8, Some(ByteOrder::Little)),
        uint8_constant(9)
    );
}

/// Rule K5: a typed 32-bit read of a cell of the other signedness is the
/// sign cast σ of the stored word, which folds a constant (`4294967295u`
/// reads as `-1`) and keeps an explicit σ of a symbolic word; a read at the
/// stored signedness is the stored value. A load term answered from the
/// cell is that same value (`LoadKind::read_cell`, R-mem through σ): only
/// the stored kind reads the stored term itself.
#[test]
fn a_32_bit_read_of_the_other_signedness_is_the_sign_cast_of_the_word() {
    use MachineIntegerType::{Int32, UInt32};
    let constant = MachineTerm::constant(u32::MAX);
    let variable = MachineTerm::Variable(Variable(613_101));
    for term in [constant, variable] {
        for (stored, read, cast) in [
            (Int32, Int32, None),
            (UInt32, UInt32, None),
            (Int32, UInt32, Some((Int32, UInt32))),
            (UInt32, Int32, Some((UInt32, Int32))),
        ] {
            let cell = stored.value_from_term(term.clone());
            let expected = match cast {
                None => term.clone(),
                Some((source, destination)) => {
                    MachineTerm::sign_cast32(source, destination, term.clone())
                }
            };
            assert_eq!(
                read.program_type().read_cell(&cell),
                Some(read.value_from_term(expected.clone())),
                "{stored:?} cell read at {read:?}"
            );
            // A load term answered from the cell is the same value: σ of
            // the stored word at the other signedness (R-mem), never the
            // stored word itself.
            let kind = LoadKind::of_type(read.program_type()).unwrap();
            assert_eq!(
                kind.reads_value(&cell),
                cast.is_none(),
                "{stored:?} cell, {read:?} load term"
            );
            assert_eq!(
                kind.read_cell(&cell),
                Some(read.value_from_term(expected.clone()))
            );
            if matches!(term, int32_constant!(_)) && cast.is_some() {
                assert_eq!(expected.constant32(), Some(u32::MAX));
            }
        }
    }
    assert_eq!(
        LoadKind::of_type(ProgramType::UInt32),
        Some(LoadKind::UInt32)
    );
    assert_eq!(LoadKind::of_type(ProgramType::Int32), Some(LoadKind::Int32));
    assert_eq!(
        LoadKind::of_type(ProgramType::Int32Pointer),
        Some(LoadKind::Int32)
    );
}

/// C11 6.5p7: a character load of a one-byte cell of the other signedness
/// reads the same eight bits. Constants fold to the reinterpreted value in
/// both directions; a symbolic cell keeps an explicit modular conversion of
/// its own term, never a fresh unrelated value.
#[test]
fn character_loads_read_a_one_byte_cell_of_the_other_signedness_as_its_bits() {
    let int8 = |value: i8| crate::kernel::int8(value as i32 as u32);
    let uint8 = |value: u8| crate::kernel::uint8(u32::from(value));
    for byte in [0u8, 1, 0x7F, 0x80, 0xC8, 0xFF] {
        assert_eq!(
            ProgramType::UInt8.read_cell(&int8(byte as i8)),
            Some(uint8(byte))
        );
        assert_eq!(
            ProgramType::Int8.read_cell(&uint8(byte)),
            Some(int8(byte as i8))
        );
        assert_eq!(
            ProgramType::Int8.read_cell(&int8(byte as i8)),
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
    let variable = MachineTerm::Variable(Variable(613_001));
    assert_eq!(
        ProgramType::UInt8.read_cell(&ProgramValue::Int8(variable.clone())),
        Some(ProgramValue::UInt8(MachineTerm::machine_integer_cast(
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            variable.clone(),
        )))
    );
    // Reading back through the original signedness is the original term.
    let Some(ProgramValue::Int8(round_trip)) = ProgramType::UInt8
        .read_cell(&ProgramValue::Int8(variable.clone()))
        .and_then(|value| ProgramType::Int8.read_cell(&value))
    else {
        panic!("a character round trip reads a signed byte");
    };
    assert_eq!(round_trip, variable);
    // No other cell gains a character view: wider integers go through the
    // byte view, and bool, pointer, and float cells stay refused. A wider
    // load reads only a cell of its own width.
    for (load, stored) in [
        (ProgramType::UInt8, crate::kernel::int16(1)),
        (ProgramType::Int8, ProgramValue::bool_constant(true)),
        (
            ProgramType::UInt8,
            ProgramValue::Float32(MachineTerm::constant(0)),
        ),
        (ProgramType::Int16, crate::kernel::uint8(1)),
        (ProgramType::Int32, crate::kernel::int16(1)),
        (
            ProgramType::UInt64,
            ProgramValue::UInt32(MachineTerm::constant(1)),
        ),
        (ProgramType::UInt16, crate::kernel::int8(1)),
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
    let int16 = |value: i16| crate::kernel::int16(value as i32 as u32);
    let uint16 = |value: u16| crate::kernel::uint16(u32::from(value));
    for half in [0u16, 1, 0x7FFF, 0x8000, 0xFFC8, 0xFFFF] {
        assert_eq!(
            ProgramType::UInt16.read_cell(&int16(half as i16)),
            Some(uint16(half))
        );
        assert_eq!(
            ProgramType::Int16.read_cell(&uint16(half)),
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
        let bits = MachineTerm::constant(word);
        assert_eq!(
            ProgramType::UInt32.read_cell(&ProgramValue::Int32(bits.clone())),
            Some(uint32(bits.clone()))
        );
        assert_eq!(
            ProgramType::Int32.read_cell(&ProgramValue::UInt32(bits.clone())),
            Some(ProgramValue::Int32(bits))
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
            ProgramType::UInt64.read_cell(&ProgramValue::Int64(MachineTerm::int64_constant(
                word as i64
            ))),
            Some(ProgramValue::UInt64(MachineTerm::uint64_constant(word)))
        );
        assert_eq!(
            ProgramType::Int64.read_cell(&ProgramValue::UInt64(MachineTerm::uint64_constant(word))),
            Some(ProgramValue::Int64(MachineTerm::int64_constant(
                word as i64
            )))
        );
    }
    let variable = MachineTerm::Variable(Variable(613_002));
    assert_eq!(
        ProgramType::UInt16.read_cell(&ProgramValue::Int16(variable.clone())),
        Some(ProgramValue::UInt16(MachineTerm::machine_integer_cast(
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            variable.clone(),
        )))
    );
    let Some(ProgramValue::Int16(round_trip)) = ProgramType::UInt16
        .read_cell(&ProgramValue::Int16(variable.clone()))
        .and_then(|value| ProgramType::Int16.read_cell(&value))
    else {
        panic!("a halfword round trip reads a signed halfword");
    };
    assert_eq!(round_trip, variable);
    let Some(ProgramValue::Int64(round_trip)) = ProgramType::UInt64
        .read_cell(&ProgramValue::Int64(variable.clone()))
        .and_then(|value| ProgramType::Int64.read_cell(&value))
    else {
        panic!("a 64-bit round trip reads a signed word");
    };
    assert_eq!(round_trip, variable);
}

/// The execution load path applies the rule: a cell stored as `signed char`
/// is read through `unsigned char` as its bits, and the reverse.
#[test]
fn execution_loads_read_character_cells_of_the_other_signedness() {
    let memory = Memory::new()
        .store(word(0), crate::kernel::int8(-56i32 as u32))
        .store(word(1), crate::kernel::uint8(200));
    assert_eq!(
        load_byte(&memory, 0, ProgramType::UInt8, Some(ByteOrder::Little)),
        ExpressionOutcome::Value(crate::kernel::uint8(200))
    );
    assert_eq!(
        load_byte(&memory, 1, ProgramType::Int8, Some(ByteOrder::Little)),
        ExpressionOutcome::Value(crate::kernel::int8(-56i32 as u32))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/byte_view_tests.rs");
}
