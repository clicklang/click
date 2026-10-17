// Scaling tests of `src/kernel/spec.rs` (module `integer_truncation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_truncation_guard_lookup_ignores_unrelated_facts() {
    let left = IntegerTerm::Variable(Variable(150_093));
    let right = IntegerTerm::Variable(Variable(150_094));
    for remainder in [false, true] {
        let expression = truncation(remainder, left.clone(), right.clone());
        let mut measured = Vec::new();
        for count in [16, 64, 256] {
            let mut assumptions = PureFactContext::new().assume_condition(
                ConditionTerm::integer_not_equal(right.clone(), IntegerTerm::constant_i64(0)),
                true,
            );
            for index in 0..count {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::integer_not_equal(
                        IntegerTerm::Variable(Variable(151_000 + index)),
                        IntegerTerm::constant_i64(0),
                    ),
                    true,
                );
            }
            let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
                capture_spec_integer_value(&CState::new(), &expression, None, &assumptions)
            });
            value.unwrap();
            measured.push(work);
        }
        assert!(
            measured.iter().all(|work| *work == measured[0]),
            "{measured:?}"
        );
    }
}
