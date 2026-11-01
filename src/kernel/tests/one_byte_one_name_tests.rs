//! Byte reads at their own types: the `int8` and `uint8` reads of one byte
//! are two loads, neither a conversion of the other, related by the native
//! 8-bit sign cast when they read the same byte (R-mem).

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn byte(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:bytes"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

fn read(offset: i64, kind: LoadKind) -> Bitvector32Term {
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    Bitvector32Term::memory_read(memory, byte(offset), kind)
}

fn constant(format: MachineIntegerType, value: i64) -> Bitvector32Term {
    Bitvector32Term::narrow_constant(format, value as u128)
}

fn equal(
    format: MachineIntegerType,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    ConditionTerm::narrow_compare(format, CompareRelation::Equal, left, right)
}

/// The signed/unsigned pairs every byte test checks: both halves of the
/// range and both of its ends.
const BYTE_PAIRS: [(i64, i64); 7] = [
    (0, 0),
    (7, 7),
    (127, 127),
    (-128, 128),
    (-56, 200),
    (-1, 255),
    (-2, 254),
];

#[test]
fn a_signed_byte_read_is_its_own_load() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let signed = Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::Int8);
    assert!(matches!(
        signed,
        Bitvector32Term::MemoryLoad(_, _, LoadKind::Int8)
    ));
    assert_eq!(signed.signed_byte_operand(), None);
    // Its canonical form is its own load's, and the read is named.
    assert_ne!(
        crate::kernel::canonical_form_of_load(memory.clone(), byte(0), LoadKind::Int8),
        crate::kernel::canonical_form_of_load(memory, byte(0), LoadKind::UInt8)
    );
    assert!(crate::kernel::eval::load_variable_for_term(&signed).is_some());
    // The native sign cast still folds a constant: the byte 0xC8 is -56.
    assert_eq!(
        Bitvector32Term::signed_byte(constant(MachineIntegerType::UInt8, 0xC8)),
        constant(MachineIntegerType::Int8, -56)
    );
}

#[test]
fn signed_and_unsigned_symbolic_reads_of_one_byte_are_two_loads() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new()
        .with_block("global:bytes", 4)
        .store(byte(1), crate::kernel::uint8(7));
    let read = |value_type| {
        let paths = evaluate_c_memory_load_paths(
            &memory,
            byte(0),
            value_type,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            false,
            false,
            None,
            None,
        );
        assert_eq!(paths.len(), 1);
        match &paths[0].outcome {
            CExpressionOutcome::Value(value) => value.clone(),
            other => panic!("{other:?}"),
        }
    };
    assert!(matches!(read(CType::UInt8), CValue::UInt8(_)));
    let CValue::Int8(signed) = read(CType::Int8) else {
        panic!("a signed byte read is int8");
    };
    assert_eq!(signed.signed_byte_operand(), None);
}

/// R-mem: a constant known of either read of a byte decides the other, and
/// refutes every other value.
#[test]
fn a_byte_constant_decides_the_other_read_of_its_byte() {
    use MachineIntegerType::{Int8, UInt8};
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = read(0, LoadKind::UInt8);
    let signed = read(0, LoadKind::Int8);
    for (signed_value, unsigned_value) in BYTE_PAIRS {
        let from_signed = PureFactContext::new().assume_condition(
            equal(Int8, signed.clone(), constant(Int8, signed_value)),
            true,
        );
        assert_eq!(
            from_signed.decide(&equal(
                UInt8,
                unsigned.clone(),
                constant(UInt8, unsigned_value)
            )),
            Some(true),
            "int8 read == {signed_value}"
        );
        assert_eq!(
            from_signed.decide(&equal(
                UInt8,
                unsigned.clone(),
                constant(UInt8, (unsigned_value + 1) % 256)
            )),
            Some(false)
        );
        let from_unsigned = PureFactContext::new().assume_condition(
            equal(UInt8, unsigned.clone(), constant(UInt8, unsigned_value)),
            true,
        );
        assert_eq!(
            from_unsigned.decide(&equal(Int8, signed.clone(), constant(Int8, signed_value))),
            Some(true),
            "uint8 read == {unsigned_value}"
        );
    }
}

/// R-mem relates only reads of the same byte: a fact about one byte's read
/// decides nothing about another byte's.
#[test]
fn reads_of_different_bytes_are_not_related() {
    use MachineIntegerType::{Int8, UInt8};
    let _session = crate::kernel::VerificationSession::enter();
    let context = PureFactContext::new().assume_condition(
        equal(UInt8, read(0, LoadKind::UInt8), constant(UInt8, 200)),
        true,
    );
    assert_eq!(
        context.decide(&equal(Int8, read(1, LoadKind::Int8), constant(Int8, -56))),
        None
    );
}

/// The native sign cast is a bijection at eight bits (R0), so a constant of
/// a conversion decides its operand whatever the operand is: every 8-bit
/// value is canonical.
#[test]
fn a_native_sign_cast_constant_decides_its_operand() {
    use MachineIntegerType::{Int8, UInt8};
    let _session = crate::kernel::VerificationSession::enter();
    let operand = Bitvector32Term::Variable(Variable(612_201));
    let signed = Bitvector32Term::signed_byte(operand.clone());
    for (signed_value, unsigned_value) in BYTE_PAIRS {
        let context = PureFactContext::new().assume_condition(
            equal(Int8, signed.clone(), constant(Int8, signed_value)),
            true,
        );
        assert_eq!(
            context.decide(&equal(
                UInt8,
                operand.clone(),
                constant(UInt8, unsigned_value)
            )),
            Some(true),
            "int8(u) == {signed_value}"
        );
    }
}
