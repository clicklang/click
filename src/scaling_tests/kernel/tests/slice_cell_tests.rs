// Scaling tests of `src/kernel/tests/slice_cell_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Storing a slice and reading it back, and the refused thin and
/// second-word reads of its cell, do work independent of other memory:
/// other blocks holding
/// slice and pointer cells, and other cells of the same block beyond the
/// slice's 16 bytes.
#[test]
fn slice_cell_store_and_read_ignore_unrelated_cells() {
    let mut samples = Vec::new();
    for size in [8_i64, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let mut memory = SymbolicMemory::new();
        for index in 0..size {
            let id = 962_000 + 4 * index as u64;
            memory = memory
                .store(
                    Address::new(
                        AddressBase::from(format!("global:other_slice{index}").as_str()),
                        AddressOffset::constant(0),
                    ),
                    ProgramValue::Pointer(wide(id, id + 1)),
                )
                .store(
                    Address::new(
                        AddressBase::from(format!("global:other_thin{index}").as_str()),
                        AddressOffset::constant(0),
                    ),
                    ProgramValue::Pointer(Pointer::new(
                        Address::symbolic(Variable(id + 2)),
                        ProgramType::UInt8Pointer,
                    )),
                )
                // Same block, after the slice's cell.
                .store(cell(16 + 8 * index), ProgramValue::UInt64(count(id + 3)));
        }
        let s = wide(961_900, 961_901);
        let ((stored, refused_read), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let stored = memory
                    .clone()
                    .store(cell(0), ProgramValue::Pointer(s.clone()));
                let read = load(&stored, 0, bytes());
                let thin = load(&stored, 0, ProgramType::UInt8Pointer);
                let word = load(&stored, 8, ProgramType::UInt64);
                (read, refused(&thin) && refused(&word))
            });
        assert_eq!(stored, ExpressionOutcome::Value(ProgramValue::Pointer(s)));
        assert!(refused_read);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "slice cell store and read work grew with unrelated cells: {samples:?}"
    );
}

/// A block of many slice cells side by side: reading one slice, and the
/// refused read of one of its words, look up only the cells that could
/// overlap the read, however many slices the block holds.
#[test]
fn slice_cell_reads_stay_flat_as_a_block_of_slices_grows() {
    let mut samples = Vec::new();
    for size in [8_i64, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let mut memory = SymbolicMemory::new();
        for index in 0..size {
            let id = 963_000 + 2 * index as u64;
            memory = store(memory, 16 * index, ProgramValue::Pointer(wide(id, id + 1)));
        }
        let middle = size / 2;
        let id = 963_000 + 2 * middle as u64;
        let ((read, word), work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                load(&memory, 16 * middle, bytes()),
                load(&memory, 16 * middle + 8, ProgramType::UInt64),
            )
        });
        assert_eq!(
            read,
            ExpressionOutcome::Value(ProgramValue::Pointer(wide(id, id + 1)))
        );
        assert!(refused(&word), "{word:?}");
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "slice cell read work grew with the block's slices: {samples:?}"
    );
}
