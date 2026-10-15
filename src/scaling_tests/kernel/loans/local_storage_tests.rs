// Scaling tests of `src/kernel/loans.rs` (module `local_storage_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn local_view_work_tracks_the_explicit_delta_not_ambient_local_storage() {
    let assumptions = PureFactContext::new();
    let mut fixed = Vec::new();
    let mut growing = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut memory = CMemory::new();
        for index in 0..size {
            memory = memory.with_block(
                view(index, 1)
                    .fact
                    .memory_range()
                    .unwrap()
                    .base()
                    .block
                    .clone(),
                4,
            );
        }
        let mut one = plan();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            one.lend_local_views(&memory, &[view(0, 1)], &assumptions)
                .unwrap();
        });
        assert!(work > 0);
        fixed.push(work);
        let mut all = plan();
        let requirements = (0..size).map(|index| view(index, 1)).collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            all.lend_local_views(&memory, &requirements, &assumptions)
                .unwrap();
            all.recover_stable_views(&assumptions, &BTreeMap::new(), &[])
                .unwrap();
        });
        growing.push(work);
    }
    assert!(
        fixed[3] <= fixed[0] * 2,
        "local loan scans ambient storage: {fixed:?}"
    );
    for pair in growing.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "local loan work exceeds its explicit delta: {growing:?}"
        );
    }
}
