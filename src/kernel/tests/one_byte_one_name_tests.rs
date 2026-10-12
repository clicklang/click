//! One byte, one name: a byte's single term is its unsigned read, and a
//! signed read is the two's-complement conversion of that term.

use super::*;

fn byte(offset: i64) -> Pointer {
    Pointer {
        block: PointerBlock::from("global:bytes"),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

#[test]
fn a_signed_byte_read_is_the_conversion_of_the_unsigned_read() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let unsigned = Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::UInt8);
    let signed = Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::Int8);
    assert_eq!(signed, Bitvector32Term::signed_byte(unsigned.clone()));
    assert_eq!(signed.signed_byte_operand(), Some(&unsigned));
    // Every other kind is its own load term.
    assert!(matches!(
        Bitvector32Term::memory_read(memory.clone(), byte(0), LoadKind::Int16),
        Bitvector32Term::MemoryLoad(_, _, LoadKind::Int16)
    ));
    // The canonical form names the one unsigned read in both.
    let canonical_signed =
        crate::kernel::canonical_form_of_load(memory.clone(), byte(0), LoadKind::Int8);
    let canonical_unsigned =
        crate::kernel::canonical_form_of_load(memory, byte(0), LoadKind::UInt8);
    assert_eq!(
        canonical_signed,
        Bitvector32Term::signed_byte(canonical_unsigned)
    );
    // Constants fold: the byte 0xC8 is -56 signed.
    assert_eq!(
        Bitvector32Term::signed_byte(Bitvector32Term::Constant(0xC8)),
        Bitvector32Term::Constant(-56i32 as u32)
    );
}

#[test]
fn a_raw_signed_byte_load_term_is_refused_a_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let raw = Bitvector32Term::MemoryLoad(memory.clone(), Box::new(byte(0)), LoadKind::Int8);
    assert_eq!(crate::kernel::eval::load_variable_for_term(&raw), None);
    let unsigned = Bitvector32Term::MemoryLoad(memory, Box::new(byte(0)), LoadKind::UInt8);
    assert!(crate::kernel::eval::load_variable_for_term(&unsigned).is_some());
}

#[test]
fn signed_and_unsigned_symbolic_reads_of_one_byte_share_its_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new()
        .with_block("global:bytes", 4)
        .store(byte(1), CValue::UInt8(Bitvector32Term::Constant(7)));
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
    let CValue::UInt8(unsigned) = read(CType::UInt8) else {
        panic!("an unsigned byte read is uint8");
    };
    let CValue::Int8(signed) = read(CType::Int8) else {
        panic!("a signed byte read is int8");
    };
    assert_eq!(signed.signed_byte_operand(), Some(&unsigned));
}

#[test]
fn signed_byte_intervals_follow_the_unsigned_byte() {
    let unsigned = Bitvector32Term::Variable(Variable(612_001));
    let signed = Bitvector32Term::signed_byte(unsigned.clone());
    let unconstrained = PureFactContext::new();
    assert_eq!(unconstrained.signed_interval(&signed), Some((-128, 127)));
    let low = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(unsigned.clone(), Bitvector32Term::Constant(100)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(unsigned.clone(), Bitvector32Term::Constant(0)),
            true,
        );
    assert_eq!(low.signed_interval(&signed), Some((0, 100)));
    let high = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(unsigned.clone(), Bitvector32Term::Constant(200)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(unsigned, Bitvector32Term::Constant(255)),
            true,
        );
    assert_eq!(high.signed_interval(&signed), Some((-56, -1)));
}
