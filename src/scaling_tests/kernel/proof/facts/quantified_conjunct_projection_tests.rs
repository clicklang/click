// Scaling tests of `src/kernel/proof/facts.rs` (module `quantified_conjunct_projection_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Selecting the guarded universal a goal drops conjuncts of costs the same
/// beside 16 or 256 unrelated guarded conjunction universals, which fill
/// the same projection index under other keys, and as many unrelated
/// universals without a conjunction.
#[test]
fn projection_lookup_is_flat_against_unrelated_quantified_facts() {
    let goal = guarded(2, 4, |k| equals(k, 7));
    let mut costs = Vec::new();
    for size in [16u32, 64, 256] {
        let mut facts = ProofFacts::from_ordered(&[]);
        for index in 0..size {
            let var = 1_000 + u64::from(index) * 2;
            facts = facts.with_fact(guarded(var, 4, |k| {
                and(at_most(k, 9), equals(k, 100 + index))
            }));
            facts = facts.with_fact(guarded(var + 1, 5 + index, |k| equals(k, 7)));
        }
        facts = facts.with_fact(guarded(1, 4, |k| and(at_most(k, 9), equals(k, 7))));
        crate::kernel::proof::reset_alpha_proposition_key_visits();
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.quantified_conjunct_projection_source(&goal).is_some()
        });
        assert!(found);
        costs.push((work, crate::kernel::proof::alpha_proposition_key_visits()));
    }
    eprintln!("projection lookup work and key visits by size: {costs:?}");
    assert!(
        costs.windows(2).all(|pair| pair[0] == pair[1]),
        "projection lookup work and key visits: {costs:?}"
    );
}
