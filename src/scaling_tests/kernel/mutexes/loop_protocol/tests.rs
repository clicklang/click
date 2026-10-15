// Scaling tests of `src/kernel/mutexes/loop_protocol.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn loop_abstraction_and_selected_join_scale_with_index_paths() {
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut context = MutexContext::new(CState::new());
        for index in 0..size {
            context = context.initialize_empty(mutex(index), 40).unwrap();
        }
        let address = mutex(size / 2);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let head = abstracted(&context, &address, false);
            let next = head
                .acquire_current(&address, &PureFactContext::new())
                .unwrap();
            head.state()
                .mutex_ledger
                .as_ref()
                .unwrap()
                .check_loop_protocol_state_since(
                    next.state().mutex_ledger.as_ref().unwrap(),
                    std::slice::from_ref(&address),
                )
                .unwrap();
        });
        samples.push(work);
    }
    assert!(samples[0] > 0);
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 512, "{samples:?}");
    }
}
