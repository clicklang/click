// Scaling tests of `src/kernel/proof/facts.rs` (module `disjunction_projection_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn projection_skips_unrelated_disjunctions_and_scalar_facts() {
    let mut costs = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut facts = ProofFacts::from_ordered(&[]);
        for index in 0..size {
            facts = facts.with_fact(or(value(100 + index * 2, 0), value(101 + index * 2, 1)));
            // Even scalar facts on a selected operand are not candidates.
            facts = facts.with_fact(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(1)),
                    Bitvector32Term::Constant(10 + index as u32),
                ),
                true,
            ));
        }
        let nested = or(value(5, 5), value(6, 6));
        let source = or(and(value(1, 1), nested.clone()), and(value(2, 2), nested));
        facts = facts.with_fact(source);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(facts.contains_disjunction_projection(&or(value(1, 1), value(2, 2))));
        });
        costs.push(work);
    }
    assert!(
        costs.iter().all(|work| *work <= costs[0] * 2),
        "projection work: {costs:?}"
    );
}
