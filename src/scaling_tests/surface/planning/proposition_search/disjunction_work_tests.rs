// Scaling tests of `src/surface/planning/proposition_search.rs` (module `disjunction_work_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// A generated unsigned-arithmetic guard is `false or bound`. Checking its
// available bound must not search unrelated facts for a proof of false.
#[test]
fn false_disjunct_does_not_scan_unrelated_context_before_available_bound() {
    let bound = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(Bitvector32Term::Variable(Variable(950_000))),
            Box::new(Bitvector32Term::Constant(20)),
        ),
        true,
    );
    let goal = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )),
        Box::new(bound.clone()),
    );
    let mut samples = Vec::new();
    for size in [32, 128, 512] {
        let mut context = PureFactContext::new().assume_proposition(bound.clone());
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::Variable(Variable(960_000 + index))),
                    Box::new(Bitvector32Term::Constant(100)),
                ),
                true,
            );
        }
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .derive_proposition(&goal)
                .expect("the bound is stated")
        });
        assert!(proof.check(&context));
        assert!(!proof.check(&context.without_exact_fact(&bound)));
        samples.push((size, work));
    }
    assert!(samples[2].1 <= samples[0].1 + 64, "{samples:?}");
}
