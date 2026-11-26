// Scaling tests of `src/kernel/tests/byte_view_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn byte_assembly_masks_symbolic_bytes_and_ignores_unrelated_memory() {
    use crate::kernel::eval::assemble_declared_uint32_after_byte_store as assemble;
    let mut samples = Vec::new();
    for size in [0, 64, 128, 512] {
        let mut memory = SymbolicMemory::new().with_declared_scalar_block(
            word(0).base.clone(),
            4,
            ProgramType::UInt32,
        );
        for byte in 0..3 {
            memory = memory.store(
                word(byte),
                ProgramValue::UInt8(OldMachineTerm::Variable(Variable(8000 + byte as u64))),
            );
        }
        for index in 0..size {
            memory = memory.with_block(format!("global:other{index}"), 4).store(
                Address::new(
                    format!("global:other{index}").into(),
                    AddressOffset::constant(0),
                ),
                ProgramValue::UInt32(index.into()),
            );
        }
        let incoming = ProgramValue::UInt8(OldMachineTerm::Variable(Variable(8003)));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            assemble(&memory, &word(3), &incoming, Some(ByteOrder::Little))
        });
        let mut expected = OldMachineTerm::constant(0);
        for byte in 0u32..4 {
            expected = OldMachineTerm::bitwise_or(
                expected,
                // Each byte's word is its zero extension.
                OldMachineTerm::unsigned_shift_left(
                    OldMachineTerm::machine_integer_cast(
                        crate::kernel::MachineIntegerType::UInt8,
                        crate::kernel::MachineIntegerType::Int32,
                        OldMachineTerm::Variable(Variable(8000 + u64::from(byte))),
                    ),
                    (8 * byte).into(),
                ),
            );
        }
        assert_eq!(result, Some((word(0), ProgramValue::UInt32(expected))));
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
        let mut memory = SymbolicMemory::new().store(
            word(0),
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(0x0102_0304_0506_0708)),
        );
        for index in 0..unrelated {
            memory = memory.store(
                Address::new(
                    AddressBase::from(format!("global:unrelated{index}").as_str()),
                    AddressOffset::constant(0),
                ),
                ProgramValue::UInt32(index.into()),
            );
            // Cells after the access in the same block are outside the range.
            memory = memory.store(
                word(8 + 4 * i64::from(index)),
                ProgramValue::UInt32(index.into()),
            );
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

#[test]
fn declared_word_read_representation_ignores_unrelated_memory() {
    use crate::kernel::{ProgramPoint, eval::declared_uint32_read_representation};
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = SymbolicMemory::new().with_declared_scalar_block(
            word(0).base.clone(),
            4,
            ProgramType::UInt32,
        );
        for index in 0..size {
            memory = memory.with_block(format!("unrelated:{index}"), 4);
        }
        let point = ProgramPoint::of_memory(&memory);
        let (equation, work) = crate::instrumentation::measure_deterministic_work(|| {
            declared_uint32_read_representation(&point, &word(0), Some(ByteOrder::Little))
        });
        assert!(equation.is_some());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn containing_cell_lookup_keeps_compact_runs_compact() {
    let value = ProgramValue::UInt64(OldMachineTerm::uint64_constant(0x0102_0304_0506_0708));
    let absent = Address::new(
        AddressBase::from("global:other"),
        AddressOffset::constant(0),
    );
    let samples = [4, 16, 64, 256].map(|count| {
        let memory = SymbolicMemory::new()
            .with_constant_run(word(0), ProgramType::UInt64, count, value.clone())
            .expect("fresh memory holds a compact word run");
        let ((hit, miss), work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                containing_integer_cell(&memory, &word(7), Some(ByteOrder::Little)),
                containing_integer_cell(&memory, &absent, Some(ByteOrder::Little)),
            )
        });
        assert_eq!(
            hit,
            Some(ContainingIntegerCell {
                pointer: word(0),
                value: value.clone(),
                byte: 7,
            })
        );
        assert_eq!(miss, None);
        work
    });
    assert_eq!(samples, [samples[0]; 4]);
}
