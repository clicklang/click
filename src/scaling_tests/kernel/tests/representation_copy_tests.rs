// Scaling tests of `src/kernel/tests/representation_copy_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn representation_copy_lookup_work_is_linear_in_the_copied_extent() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for cells in [4_u32, 8, 16, 32, 64] {
        let entry = source_with_cells(CMemory::new(), "extent-source", cells);
        let (lookup, transfer) = copy_lookup_work(
            &entry,
            &CMemory::new(),
            "extent-source",
            "extent-destination",
            cells,
        );
        lookups.push(lookup);
        transfers.push(transfer);
        // One unit for the range query, one per copied cell it visits.
        assert_eq!(
            lookup,
            1 + cells as usize,
            "copied-extent lookup work: {lookups:?}; whole transfer: {transfers:?}"
        );
    }
    assert!(
        lookups.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
        "copied-extent lookup work grew faster than the extent: {lookups:?}"
    );
}

#[test]
fn fixed_representation_copy_lookup_work_is_independent_of_unrelated_memory() {
    let mut lookups = Vec::new();
    let mut transfers = Vec::new();
    for unrelated in [8_u32, 32, 128, 512] {
        let mut memory = source_with_cells(CMemory::new(), "fixed-source", 4);
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
