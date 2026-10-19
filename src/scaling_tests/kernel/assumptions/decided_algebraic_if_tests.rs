// Scaling tests of `src/kernel/assumptions.rs` (module `decided_algebraic_if_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Once an `if` equation decided a condition, each later fact reads only its
/// own conditionals: assuming one more fact costs the same however many
/// unrelated decided facts the context holds.
#[test]
fn a_decided_conditional_costs_a_later_fact_only_its_own_conditions() {
    let mut work = Vec::new();
    for size in [8u64, 16, 32, 64] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(equal(view(1_000 + index, 2_000 + index), some(3_000 + index)));
        }
        let fact = equal(view(1_000, 2_000), some(9_999));
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            context.clone().assume_proposition(fact.clone())
        });
        work.push(measured);
    }
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + pair[0] / 4),
        "work grew with unrelated decided facts: {work:?}"
    );
}
