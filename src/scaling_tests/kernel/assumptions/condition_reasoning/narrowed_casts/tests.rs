// Scaling tests of `src/kernel/assumptions/condition_reasoning/narrowed_casts.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// The rule decides two bounds about the operand and visits nothing else:
// its work does not grow with unrelated facts in the context.
#[test]
fn narrowed_cast_identity_work_is_independent_of_unrelated_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(170_004));
    let byte = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::UInt8, x.clone());
    let mut work = Vec::new();
    for unrelated in [4u32, 64, 1024] {
        let mut context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(x.clone(), Bitvector32Term::Constant(255)),
                true,
            );
        for index in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(171_000 + u64::from(index))),
                    Bitvector32Term::Constant(index),
                ),
                true,
            );
        }
        let (carrier, cost) = crate::instrumentation::measure_deterministic_work(|| {
            context.narrowed_cast_carrier(&byte)
        });
        assert_eq!(carrier, Some(x.clone()));
        // Filing an equality that names the conversion relates it to
        // its operand with the same bounded decisions.
        let name = Bitvector32Term::Variable(Variable(170_005));
        let (related, filing) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .clone()
                .assume_condition(ConditionTerm::equal(name.clone(), byte.clone()), true)
        });
        assert_eq!(
            related.decide(&ConditionTerm::equal(name, x.clone())),
            Some(true)
        );
        work.push(cost.saturating_add(filing));
    }
    assert!(
        work[2] <= work[0] * 2 + 16,
        "narrowed cast identity work grew with unrelated facts: {work:?}"
    );
}
