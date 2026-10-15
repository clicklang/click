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
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for element in 0..size {
                record.record(&at("local:array", element * 4), 4);
            }
        });
        assert!(record.covers(&at("local:array", 0), u32::try_from(size * 4).unwrap()));
        assert!(
            work <= 4 * usize::try_from(size).unwrap(),
            "recording {size} elements cost {work} work units"
        );
    }
}
