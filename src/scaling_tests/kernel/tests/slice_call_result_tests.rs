// Scaling tests of `src/kernel/tests/slice_call_result_tests.rs`:
// deterministic work measured at several input sizes. Included into its
// `scaling_tests` module; see "Scaling tests" in `docs/internals/testing.md`.

use super::*;

/// Naming a slice by one variable builds its thin part and its count from
/// that variable alone, and a fact about that count is decided by the count's
/// own index entry: the work is the same however many other named slices and
/// facts about their counts exist.
#[test]
fn a_named_slice_ignores_unrelated_slices_and_facts() {
    let mut samples = Vec::new();
    for size in [8_u64, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let mut context = PureFactContext::new();
        let mut others = Vec::new();
        for index in 0..size {
            let variable = Variable(965_000 + index);
            others.push(named_slice(bytes(), variable));
            context = context.assume_condition(
                OldConditionTerm::uint64_equal(
                    OldMachineTerm::Variable(variable.element_count()),
                    OldMachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let variable = Variable(964_900);
        let context = context.assume_condition(
            OldConditionTerm::uint64_equal(
                OldMachineTerm::Variable(variable.element_count()),
                OldMachineTerm::uint64_constant(7),
            ),
            true,
        );
        let ((slice, decided), work) = crate::instrumentation::measure_deterministic_work(|| {
            let slice = named_slice(bytes(), variable);
            let count = slice.len().expect("a named slice has a count").clone();
            let decided = context.decide(&OldConditionTerm::uint64_equal(
                count,
                OldMachineTerm::uint64_constant(7),
            ));
            (slice, decided)
        });
        assert_eq!(
            slice.len(),
            Some(&OldMachineTerm::Variable(variable.element_count()))
        );
        assert_eq!(decided, Some(true));
        assert_eq!(others.len() as u64, size);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "naming a slice grew with unrelated slices and facts: {samples:?}"
    );
}
