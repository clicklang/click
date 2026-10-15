// Scaling tests of `src/surface/proof/fixed_state_proofs/fact_transport.rs` (module `path_condition_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn compound_transport_target_work_scales_with_explicit_leaves() {
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let facts = PureFactContext::new().assume_proposition(source.clone());
    let mut previous = 0;
    for size in [16, 64, 256, 1024] {
        let mut level = vec![source.clone(); size];
        while level.len() > 1 {
            level = level
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| Proposition::And(Box::new(pair[0].clone()), Box::new(pair[1].clone())))
                .collect();
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            certified_fact_transport_reaches(&source, &level[0], None, &facts)
        });
        assert!(proved);
        assert!(work >= size);
        if previous > 0 {
            assert!(work <= 4 * previous + 4, "{size}: {work} after {previous}");
        }
        previous = work;
    }
}
