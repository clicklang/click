// Scaling tests of `src/kernel/reasoning/path_facts.rs` (module `mandatory_integer_obligation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn prepared_path_extensions_with_new_facts_and_obligations_build_only_the_delta() {
    let mut samples = Vec::new();
    for size in [8usize, 16, 32] {
        let mut ambient_samples = Vec::new();
        for ambient in [0usize, 128, 512] {
            let mut base = PureFactContext::new();
            for index in 0..ambient {
                base = base.assume_proposition(Proposition::Predicate {
                    name: format!("ambient_{index}"),
                    arguments: vec![],
                });
            }
            let before = context_rebuild_entries();
            let ((facts, obligations, context), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut facts = ExecutionFacts::new();
                    let mut obligations = Vec::new();
                    let mut context = base.clone();
                    for index in 0..size {
                        let incoming_facts = ExecutionFacts::from(vec![ExecutionPureFact::new(
                            Proposition::Predicate {
                                name: format!("fact_{index}"),
                                arguments: vec![],
                            },
                        )]);
                        let incoming_obligations =
                            vec![ProofObligation::new(Proposition::Predicate {
                                name: format!("obligation_{index}"),
                                arguments: vec![],
                            })];
                        let merged = merge_prepared_execution_path(
                            &facts,
                            &obligations,
                            &incoming_facts,
                            &incoming_obligations,
                            &base,
                            &context,
                            &context,
                        )
                        .unwrap();
                        assert_eq!(merged.changed_obligations, vec![index]);
                        facts = merged.facts;
                        obligations = merged.obligations;
                        context = merged.assumptions;
                    }
                    (facts, obligations, context)
                });
            let entries = context_rebuild_entries() - before;
            assert_eq!(entries, 2 * size);
            assert_eq!(
                context,
                assumptions_with_path_context(&base, &facts, &obligations)
            );
            ambient_samples.push((entries, work));
        }
        assert!(
            ambient_samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{ambient_samples:?}"
        );
        samples.push(ambient_samples[0]);
    }
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= 2 * pair[0].1 + 32),
        "{samples:?}"
    );
}
