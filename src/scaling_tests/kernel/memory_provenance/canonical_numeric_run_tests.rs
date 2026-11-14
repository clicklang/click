// Scaling tests of `src/kernel/memory_provenance.rs` (module `canonical_numeric_run_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn deep_canonicalization_preserves_numeric_load_and_copy_runs() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(crate::kernel::Variable(7_629_000));
    for element_type in [
        ProgramType::Int8,
        ProgramType::UInt8,
        ProgramType::Int16,
        ProgramType::UInt16,
        ProgramType::Int32,
        ProgramType::UInt32,
        ProgramType::Int64,
        ProgramType::UInt64,
        ProgramType::Int128,
        ProgramType::UInt128,
        ProgramType::Float32,
        ProgramType::Float64,
    ] {
        let width = element_type.byte_width();
        // A retained observable cell deliberately defeats the generic
        // uniform-source representative argument, even though every
        // minted numeric run value remains an atomic load variable.
        let source = intern_c_memory(CMemory::new().store(base.clone(), crate::kernel::uint8(7)));
        for mode in [
            RunValueMode::Load,
            RunValueMode::Copy {
                source_base: base.offset_by_bytes(width),
            },
        ] {
            let mut costs = Vec::new();
            for size in [16, 64, 4096, 22208, 1048576] {
                let mut holes = IndexIntervals::default();
                holes.insert(3);
                let run = CellRun::new_with_mode(
                    base.clone(),
                    width,
                    element_type,
                    size,
                    source.clone(),
                    mode.clone(),
                    holes,
                );
                let mut memory = CMemory::new();
                std::sync::Arc::make_mut(&mut memory.cells).add_run(run.clone());
                let (canonical, work) = crate::instrumentation::measure_deterministic_work(|| {
                    canonical_c_memory_deep(&memory)
                });
                assert_eq!(canonical, memory);
                for index in [0, 1, size - 1] {
                    let value = run.value(index);
                    let bits = match &value {
                        ProgramValue::Int8(bits)
                        | ProgramValue::UInt8(bits)
                        | ProgramValue::Int16(bits)
                        | ProgramValue::UInt16(bits)
                        | ProgramValue::Int32(bits)
                        | ProgramValue::UInt32(bits)
                        | ProgramValue::Int64(bits)
                        | ProgramValue::UInt64(bits)
                        | ProgramValue::Int128(bits)
                        | ProgramValue::UInt128(bits)
                        | ProgramValue::Float32(bits)
                        | ProgramValue::Float64(bits) => bits,
                        _ => unreachable!("numeric cell"),
                    };
                    // Scalar run values retain the read even when checking
                    // can resolve its source to a stored literal.
                    assert!(matches!(
                        bits,
                        MachineTerm::MemoryLoad(..) | MachineTerm::Variable(_)
                    ));
                    assert_eq!(canonical.cells.get(&run.slot_pointer(index)), Some(value));
                }
                assert!(canonical.cells.get(&run.slot_pointer(3)).is_none());
                costs.push((size, work));
            }
            assert!(
                costs.iter().all(|(_, work)| *work <= costs[0].1 + 128),
                "{costs:?}"
            );
        }
    }
}
