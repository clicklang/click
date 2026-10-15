// Scaling tests of `src/kernel/mutexes/loop_protocol.rs` (module `loop_rule_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn loop_guard_projection_uses_indexed_definition_lookup() {
    let (top, _, definition) = top_and_next();
    let mut samples = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut definitions = (0..size)
            .map(|index| {
                CCompositeResourceDefinition::new(
                    format!("unrelated-{index:05}"),
                    vec![],
                    None,
                    false,
                    vec![],
                    vec![],
                )
            })
            .collect::<Vec<_>>();
        definitions.push(definition.clone());
        definitions.sort_by(|left, right| left.name().cmp(right.name()));
        let mut state = top.clone();
        for index in 0..size {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(CResourceFact::own(CResource::Token {
                    name: format!("unrelated-token-{index}"),
                    arguments: vec![].into(),
                }));
        }
        let (projection, work) = crate::instrumentation::measure_deterministic_work(|| {
            loop_instance_guard(&state, &instance(0), &definitions, &PureFactContext::new())
                .unwrap()
        });
        let (mutex, condition) = projection.unwrap();
        assert_eq!(mutex, address());
        assert_eq!(
            crate::kernel::loops::condition_is_decided(&PureFactContext::new(), &condition),
            Some(false)
        );
        samples.push(work);
    }
    assert!(samples[0] > 0, "projection must charge its work");
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}
