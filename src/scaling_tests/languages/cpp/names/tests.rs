// Scaling tests of `src/languages/cpp/names.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn collision_resolution_work_scales_with_declarations_and_identity_bytes() {
    for size in [8, 32, 128, 512] {
        let ids = (0..size)
            .map(|i| format!("scope_{i:04}"))
            .collect::<Vec<_>>();
        let (names, work) = crate::instrumentation::measure_deterministic_work(|| {
            ResolvedNames::new(ids.iter().map(|id| (id.as_str(), "same")))
        });
        let names = names.unwrap();
        assert_eq!(
            names
                .0
                .values()
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
            size
        );
        let bytes = ids.iter().map(String::len).sum::<usize>();
        assert!(
            work >= bytes && work <= bytes + 3 * size,
            "size {size}: {work}"
        );
    }
}
