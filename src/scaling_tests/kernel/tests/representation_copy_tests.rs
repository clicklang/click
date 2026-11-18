// Scaling tests of `src/kernel/tests/representation_copy_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn representation_copy_lookup_work_is_linear_in_the_copied_span() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for cells in [4_u32, 8, 16, 32, 64] {
        let entry = source_with_cells(SymbolicMemory::new(), "span-source", cells);
        let (lookup, transfer) = copy_lookup_work(
            &entry,
            &SymbolicMemory::new(),
            "span-source",
            "span-destination",
            cells,
        );
        lookups.push(lookup);
        transfers.push(transfer);
        // One unit for the range query, one per copied cell it visits.
        assert_eq!(
            lookup,
            1 + cells as usize,
            "copied-span lookup work: {lookups:?}; whole transfer: {transfers:?}"
        );
    }
    assert!(
        lookups.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
        "copied-span lookup work grew faster than the span: {lookups:?}"
    );
}

#[test]
fn fixed_representation_copy_lookup_work_is_independent_of_unrelated_memory() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for unrelated in [8_u32, 32, 128, 512] {
        let mut memory = source_with_cells(SymbolicMemory::new(), "fixed-source", 4);
        for index in 0..unrelated {
            memory = memory.store(cell(&format!("unrelated-{index}"), 0), cell_value(index));
            // Source-block cells past the copied range are not visited either.
            memory = memory.store(cell("fixed-source", 4 + index), cell_value(index));
        }
        let (lookup, transfer) =
            copy_lookup_work(&memory, &memory, "fixed-source", "fixed-destination", 4);
        lookups.push(lookup);
        transfers.push(transfer);
    }
    assert!(
        lookups.iter().all(|work| *work == 5),
        "fixed-copy lookup work grew with unrelated memory: {lookups:?}; whole transfer: {transfers:?}"
    );
    assert!(
        transfers.iter().all(|work| *work == transfers[0]),
        "fixed-copy transfer work grew with unrelated memory: {transfers:?}; lookups: {lookups:?}"
    );
}

#[test]
fn replacing_copy_initialization_visits_only_the_copied_runs() {
    let source = heap_pointer("local:copy-source");
    let destination = heap_pointer("local:copy-destination");
    let assumptions = PureFactContext::new();
    let mut measurements = Vec::new();
    for count in [4u32, 16, 64] {
        let mut samples = Vec::new();
        for unrelated in [0u32, 64, 256] {
            let mut entry = SymbolicMemory::new();
            for index in 0..unrelated {
                entry =
                    entry.with_initialized_object(&heap_pointer(&format!("unrelated-{index}")), 1);
                entry = entry
                    .with_initialized_object(&source.offset_by_bytes(2 * count + 2 * index), 1);
            }
            for index in 0..count {
                entry = entry.with_initialized_object(&source.offset_by_bytes(2 * index), 1);
            }
            entry = entry.with_initialized_object(&destination, 2 * count + 1);
            let range = MemoryRange::new_with_element_width(
                destination.clone(),
                0u32.into(),
                (2 * count).into(),
                1,
            );
            let copy = crate::kernel::primitives::RepresentationCopyRange {
                destination: destination.clone(),
                source: source.clone(),
                bytes: 2 * count,
            };
            let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
                entry.with_call_memory_havoc_with_copy(
                    Variable(100),
                    &[range],
                    &assumptions,
                    None,
                    Some(&copy),
                )
            });
            for index in 0..count {
                assert!(after.has_initialized_bytes_at(&destination.offset_by_bytes(2 * index), 1));
                assert!(
                    !after.has_initialized_bytes_at(&destination.offset_by_bytes(2 * index + 1), 1)
                );
            }
            assert!(after.has_initialized_bytes_at(&destination.offset_by_bytes(2 * count), 1));
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "fixed span: {samples:?}"
        );
        measurements.push(samples[0]);
    }
    assert!(
        measurements.windows(2).all(|pair| pair[1] <= 4 * pair[0]),
        "{measurements:?}"
    );
}

#[test]
fn mixed_bit_field_copy_work_tracks_named_bytes() {
    let source = heap_pointer("local:bit-source");
    let destination = heap_pointer("local:bit-destination");
    let full_mask = std::num::NonZeroU8::MAX;
    let mut measurements = Vec::new();
    for words in [4u32, 16, 64] {
        let size = 4 * words;
        let masks: Vec<_> = (0..words).map(|index| (4 * index + 1, full_mask)).collect();
        let scalars: Vec<_> = (0..words)
            .map(|index| {
                AggregateField::new(&format!("scalar{index}"), 4 * index + 2, ProgramType::UInt8)
            })
            .collect();
        let mut samples = Vec::new();
        for unrelated in [0, 64, 256] {
            let mut memory = SymbolicMemory::new()
                .with_uninitialized_block(source.base.clone(), size)
                .with_uninitialized_block(destination.base.clone(), size);
            for index in 0..unrelated {
                let address = heap_pointer(&format!("local:bit-unrelated-{index}"));
                memory = memory.store(address, crate::kernel::uint8(1));
            }
            for &(offset, _) in &masks {
                memory = memory.store(source.offset_by_bytes(offset), crate::kernel::uint8(7));
            }
            for field in &scalars {
                memory = memory.store(
                    source.offset_by_bytes(field.offset_bytes()),
                    crate::kernel::uint8(8),
                );
            }
            let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.copy_local_bit_field_record(&source, &destination, size, &masks, &scalars)
            });
            let copied = copied.unwrap();
            for &(offset, _) in &masks {
                assert_eq!(
                    copied.known_value(&destination.offset_by_bytes(offset)),
                    Some(crate::kernel::uint8(7))
                );
                assert!(
                    !copied.has_initialized_bytes_at(&destination.offset_by_bytes(offset - 1), 1)
                );
            }
            for field in &scalars {
                assert_eq!(
                    copied.known_value(&destination.offset_by_bytes(field.offset_bytes())),
                    Some(crate::kernel::uint8(8))
                );
            }
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
        measurements.push(samples[0]);
    }
    assert!(
        measurements
            .windows(2)
            .all(|pair| pair[0] < pair[1] && pair[1] <= 4 * pair[0]),
        "{measurements:?}"
    );
}
