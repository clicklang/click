// Scaling tests of `src/kernel/proof/fact_keys.rs` (module `proposition_identity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn alpha_identity_work_scales_with_nested_binder_depth() {
    let make = |depth: u64, offset: u64| {
        let mut proposition = equal(
            Bitvector32Term::Variable(Variable(offset + depth - 1)),
            Bitvector32Term::Constant(1),
        );
        for index in (0..depth).rev() {
            proposition = forall(offset + index, proposition);
        }
        proposition
    };
    let mut work = Vec::new();
    for depth in [8, 16, 32, 64] {
        let left = make(depth, 20_000);
        let right = make(depth, 30_000);
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(propositions_are_alpha_equal(&left, &right));
        });
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 3 + 32, "alpha identity work: {work:?}");
    }
}
