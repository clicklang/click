// A nonmatching literal bound rejects a condition candidate before visiting
// the candidate getter's model pointer operands.
use super::*;

#[test]
fn rejecting_comparison_bound_ignores_unrelated_getter_payload() {
    let _session = crate::kernel::VerificationSession::enter();
    let x = Bitvector32Term::Variable(Variable(9_991_011));
    let y = Bitvector32Term::Variable(Variable(9_991_012));
    for mirrored in [false, true] {
        let mut baseline = None;
        for size in [4, 16, 64, 256] {
            let fact = ConditionTerm::signed_less_equal(
                getter(size),
                Bitvector32Term::Constant(2147483646),
            );
            let goal = if mirrored {
                ConditionTerm::signed_greater_equal(y.clone(), x.clone())
            } else {
                ConditionTerm::signed_less_equal(x.clone(), y.clone())
            };
            let context = PureFactContext::new().assume_condition(fact.clone(), true);
            let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.condition_matches(&fact, &goal)
            });
            assert!(!matched);
            if let Some(baseline) = baseline {
                assert_eq!(
                    work, baseline,
                    "{size} getter operands, mirrored={mirrored}"
                );
            } else {
                baseline = Some(work);
            }
        }
    }
}
