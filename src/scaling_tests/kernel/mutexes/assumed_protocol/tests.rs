// Scaling tests of `src/kernel/mutexes/assumed_protocol.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn abstract_protocol_transitions_ignore_unrelated_resource_frames() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let (mut state, protocol) = input();
        for index in 0..size {
            state.resources =
                state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (held, guard) = protocol.acquire(&state, &assumptions).unwrap();
                let released = protocol.release(&held.state, &guard, &assumptions).unwrap();
                protocol.check_return(&released.state).unwrap();
                released
            })
        });
        assert_eq!(returned.state.resources.facts().len(), size + 1);
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "abstract protocol scans unrelated resources: {samples:?}"
        );
    }
}

#[test]
fn opaque_runtime_transitions_ignore_unrelated_resource_frames() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let (mut state, protocol) = input();
        for index in 0..size {
            state.resources =
                state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (held, _) =
                    opaque_runtime_transition(&state, protocol.mutex(), true, &assumptions)
                        .unwrap();
                let (released, _) =
                    opaque_runtime_transition(&held, protocol.mutex(), false, &assumptions)
                        .unwrap();
                protocol.check_return(&released).unwrap();
                released
            })
        });
        assert_eq!(returned.resources.facts().len(), size + 1);
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "opaque runtime transition scans unrelated resources: {samples:?}"
        );
    }
}
