// Scaling tests of `src/kernel/mutexes/direct_loop_guard_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn direct_loop_guard_lookup_ignores_unrelated_mutexes() {
    let mut measurements = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut context = MutexContext::new(entry());
        for index in 1..size {
            context = context.initialize_empty(address(index), 40).unwrap();
        }
        let top = head(context.state(), 706);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            MutexContext::new(top).acquire_current(&address(0), &PureFactContext::new())
        });
        assert!(result.is_ok());
        measurements.push(work);
    }
    assert!(
        measurements[3] <= measurements[0] * 2 + 64,
        "indexed lookup work grew with unrelated mutexes: {measurements:?}"
    );
}
