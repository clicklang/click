// Scaling tests of `src/kernel/tests/byte_view_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn byte_assembly_masks_symbolic_bytes_and_ignores_unrelated_memory() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let mut samples = Vec::new();
    for size in [0, 64, 128, 512] {
        let mut memory = CMemory::new().with_declared_scalar_block(word(0).block, 4, CType::UInt32);
        for byte in 0..3 {
            memory = memory.store(
                word(byte),
                CValue::UInt8(Bitvector32Term::Variable(Variable(8000 + byte as u64))),
            );
        }
        for index in 0..size {
            memory = memory.with_block(format!("global:other{index}"), 4).store(
                Pointer {
                    block: format!("global:other{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::UInt32(index.into()),
            );
        }
        let incoming = CValue::UInt8(Bitvector32Term::Variable(Variable(8003)));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little))
        });
        let mut expected = Bitvector32Term::Constant(0);
        for byte in 0u32..4 {
            expected = Bitvector32Term::bitwise_or(
                expected,
                Bitvector32Term::unsigned_shift_left(
                    Bitvector32Term::bitwise_and(
                        Bitvector32Term::Variable(Variable(8000 + u64::from(byte))),
                        0xFFu32.into(),
                    ),
                    (8 * byte).into(),
                ),
            );
        }
        assert_eq!(result, Some((word(0), CValue::UInt32(expected))));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn containing_cell_lookup_work_is_independent_of_unrelated_cells() {
    let mut works = Vec::new();
    for unrelated in [8_u32, 32, 128, 512] {
        let mut memory = CMemory::new().store(
            word(0),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0x0102_0304_0506_0708)),
        );
        for index in 0..unrelated {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::from(format!("global:unrelated{index}").as_str()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::UInt32(index.into()),
            );
            // Cells after the access in the same block are outside the range.
            memory = memory.store(word(8 + 4 * i64::from(index)), CValue::UInt32(index.into()));
        }
        let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
            containing_integer_cell(&memory, &word(6), Some(ByteOrder::Little))
        });
        assert_eq!(cell.map(|cell| cell.byte), Some(6));
        works.push(work);
    }
    assert!(
        works.windows(2).all(|pair| pair[0] == pair[1]),
        "containing-cell lookup work grew with unrelated cells: {works:?}"
    );
}
