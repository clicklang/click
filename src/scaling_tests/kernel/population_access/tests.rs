// Scaling tests of `src/kernel/population_access.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn selected_scope_work_is_logarithmic_and_close_restores_the_same_root() {
    for size in [8usize, 32, 128, 512] {
        let mut access = PopulationAccess::default();
        for index in 0..size {
            access = access.open(key(index)).unwrap();
        }
        let (next, work) =
            crate::persistent::measure_persistent_work(|| access.open(key(size)).unwrap());
        assert!(
            work > 0 && work < 20 * (size.ilog2() as usize + 1),
            "size {size}: {work}"
        );
        let (restored, work) =
            crate::persistent::measure_persistent_work(|| next.close(&key(size)).unwrap());
        assert_eq!(restored, access);
        assert_eq!(work, 0);
    }
}
