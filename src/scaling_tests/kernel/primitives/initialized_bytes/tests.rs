// Scaling tests of `src/kernel/primitives/initialized_bytes.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn recording_scales_with_the_merged_runs_not_the_record() {
    // Each store into a fresh block, then one store per element of one
    // array: the work per record is the few runs it merges, whatever
    // size the record has reached.
    for size in [64i64, 512, 4096] {
        let mut record = InitializedBytes::default();
        for block in 0..size {
            record.record(&at(&format!("local:other{block}"), 0), 4);
        }
        // Building an address admits its block: that is the caller's work.
        let elements = (0..size)
            .map(|element| at("local:array", element * 4))
            .collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for element in &elements {
                record.record(element, 4);
            }
        });
        assert!(record.covers(&at("local:array", 0), u32::try_from(size * 4).unwrap()));
        assert!(
            work <= 4 * usize::try_from(size).unwrap(),
            "recording {size} elements cost {work} work units"
        );
    }
}

#[test]
fn partial_byte_updates_follow_the_selected_address_and_join_delta() {
    let mut measurements = Vec::new();
    for size in [64i64, 512, 4096] {
        let mut left = InitializedBytes::default();
        for offset in 1..=size {
            left.record_mask(&at("local:flags", offset), 1);
            left.record_mask(&at(&format!("local:other{offset}"), 0), 2);
        }
        let target = at("local:flags", 0);
        left.record_mask(&target, 1);
        let mut right = left.clone();
        let (joined, work) = crate::instrumentation::measure_deterministic_work(|| {
            right.record_mask(&target, 2);
            left.intersection(&right)
        });
        assert_eq!(joined.mask_at(&target), 1);
        assert_eq!(joined.mask_at(&at("local:flags", size)), 1);
        measurements.push(work);
    }
    assert!(measurements[0] > 0);
    assert!(
        measurements.windows(2).all(|pair| pair[0] == pair[1]),
        "{measurements:?}"
    );
}

#[test]
fn representation_copy_reads_only_partial_bytes_in_the_selected_span() {
    let source_address = at("local:source", 2);
    let destination_address = at("local:destination", 1);
    let mut measurements = Vec::new();
    for size in [64i64, 512, 4096] {
        let mut source = InitializedBytes::default();
        let mut destination = InitializedBytes::default();
        for offset in 4..=size {
            source.record_mask(&at("local:source", offset), 1);
            source.record_mask(&at(&format!("local:other{offset}"), 0), 2);
            destination.record_mask(&at("local:destination", offset), 4);
        }
        source.set_partial(source_address.clone(), 3, Some(crate::kernel::uint8(1)));
        destination.record_mask(&destination_address.offset_by_bytes(1), 8);
        let (copied, work) = crate::instrumentation::measure_deterministic_work(|| {
            destination.copy_exact_range_from(&source, &source_address, &destination_address, 2)
        });
        assert_eq!(copied, Some(()));
        let byte = destination.partial_byte(&destination_address).unwrap();
        assert_eq!(byte.mask, 3);
        assert_eq!(byte.value, Some(crate::kernel::uint8(1)));
        assert_eq!(
            destination.mask_at(&destination_address.offset_by_bytes(1)),
            0
        );
        assert_eq!(destination.mask_at(&at("local:destination", size)), 4);
        measurements.push(work);
    }
    assert!(measurements[0] > 0);
    assert!(
        measurements.windows(2).all(|pair| pair[0] == pair[1]),
        "{measurements:?}"
    );
}
