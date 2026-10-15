// Scaling tests of `src/kernel/named_authority.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn alias_lookup_does_not_scan_unrelated_resources() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let fact = authority(1);
        let mut state = CState::new();
        state.resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        for index in 0..size {
            state.resources =
                state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let ((result, deterministic), persistent) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let aliases = NamedMutexAuthorities::new()
                        .bind(Variable(1), &fact, &state)
                        .unwrap();
                    aliases.resolve(Variable(1), &state).cloned()
                })
            });
        assert_eq!(result, Some(fact));
        work.push((deterministic, persistent));
    }
    assert!(work[2].0 <= work[0].0 + 32, "alias lookup work: {work:?}");
    assert!(work[2].1 <= work[0].1 + 32, "alias index work: {work:?}");
}
