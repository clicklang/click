// Scaling tests of `src/kernel/proof/execution.rs` (module `automatic_lifetime_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn automatic_lifetime_end_consumes_only_local_construction_ownership() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let pointer = CMemory::local_pointer("selected");
        let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer,
            0u32.into(),
            16u32.into(),
            1,
        ));
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for i in 0..size {
            resources = resources
                .unchecked_with_fact(CResourceFact::own_token(format!("unrelated_{i}"), vec![]));
        }
        let state = CState::new()
            .with_local("selected", int32(0))
            .with_memory(CMemory::new().with_block("local:selected", 16))
            .with_resource_context(resources);
        let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            core.record_automatic_lifetime_end(&state, &["selected".into()])
                .unwrap()
        });
        assert!(
            !after
                .resources()
                .satisfies_fact(&owner, &PureFactContext::new())
        );
        assert!(after.resources().satisfies_fact(
            &CResourceFact::own_token("unrelated_0".into(), vec![]),
            &PureFactContext::new()
        ));
        assert!(!after.memory().has_block(&"local:selected".into()));
        let events = core.execution_evidence[0].to_vec();
        let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = &events[0] else {
            unreachable!()
        };
        assert_eq!(end.advance_checked(&state), Some(after.clone()));
        let mut forged = end.clone();
        forged.after_state = after.with_resource_context(state.resources().clone());
        assert!(forged.advance_checked(&state).is_none());
        samples.push((size, work));
    }
    eprintln!("local construction retirement (N, units): {samples:?}");
    assert!(
        samples.iter().all(|(_, work)| *work <= samples[0].1 + 64),
        "{samples:?}"
    );
}

#[test]
fn automatic_lifetime_event_ignores_unrelated_locals_and_checks_exact_states() {
    let samples = [8, 16, 32, 64].map(|size| {
        let mut state = CState::new()
            .with_local("selected", int32(5))
            .with_memory(CMemory::new().with_block("local:selected", 4));
        for i in 0..size {
            state = state.with_local(format!("other_{i}"), int32(9));
        }
        let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            core.record_automatic_lifetime_end(&state, &["selected".to_string()])
                .unwrap()
        });
        assert!(after.locals().get("selected").is_none());
        assert!(!after.memory().has_block(&"local:selected".into()));
        assert_eq!(after.locals().get("other_0"), Some(&int32(9)));
        let events = core.execution_evidence[0].to_vec();
        let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = &events[0] else {
            panic!("missing lifetime evidence")
        };
        assert_eq!(end.advance_checked(&state), Some(after.clone()));
        assert!(end.advance_checked(&after).is_none());
        let mut forged = end.clone();
        forged.after_state = state.clone();
        assert!(forged.advance_checked(&state).is_none());
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples
            .iter()
            .enumerate()
            .all(|(i, work)| *work <= samples[0] + i),
        "{samples:?}"
    );
}
