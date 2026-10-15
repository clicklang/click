// Scaling tests of `src/kernel/memory_provenance.rs` (module `canonical_numeric_run_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn deep_canonicalization_preserves_numeric_load_and_copy_runs() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(crate::kernel::Variable(7_629_000));
    for element_type in [
        CType::Int8,
        CType::UInt8,
        CType::Int16,
        CType::UInt16,
        CType::Int32,
        CType::UInt32,
        CType::Int64,
        CType::UInt64,
        CType::Int128,
        CType::UInt128,
        CType::Float32,
        CType::Float64,
    ] {
        let width = element_type.byte_width();
        // A retained observable cell deliberately defeats the generic
        // uniform-source representative argument, even though every
        // minted numeric run value remains an atomic load variable.
        let source = intern_c_memory(
            CMemory::new().store(base.clone(), CValue::UInt8(Bitvector32Term::Constant(7))),
        );
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
                        CValue::Int8(bits)
                        | CValue::UInt8(bits)
                        | CValue::Int16(bits)
                        | CValue::UInt16(bits)
                        | CValue::Int32(bits)
                        | CValue::UInt32(bits)
                        | CValue::Int64(bits)
                        | CValue::UInt64(bits)
                        | CValue::Int128(bits)
                        | CValue::UInt128(bits)
                        | CValue::Float32(bits)
                        | CValue::Float64(bits) => bits,
                        _ => unreachable!("numeric cell"),
                    };
                    assert_eq!(canonicalize_atomic_loads(bits), *bits);
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
