// Scaling coverage for constant-bound selection beside earlier outcomes.
use super::*;

#[test]
fn outcome_constant_bounds_keep_a_compact_selected_context() {
    for size in [4u32, 32, 64, 256] {
        let x = Bitvector32Term::Variable(Variable(786_001));
        let lower = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(x.clone()),
            ),
            true,
        );
        let upper = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(x.clone()),
                Box::new(Bitvector32Term::Constant(1000)),
            ),
            true,
        );
        let mut facts = PureFactContext::new()
            .assume_proposition(lower.clone())
            .assume_proposition(upper.clone());
        for index in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(x.clone()),
                    Box::new(Bitvector32Term::Subtract(
                        Box::new(x.clone()),
                        Box::new(Bitvector32Term::Constant(index)),
                    )),
                ),
                true,
            );
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(x.clone()),
                Box::new(Bitvector32Term::Subtract(
                    Box::new(x),
                    Box::new(Bitvector32Term::Constant(size)),
                )),
            ),
            true,
        );
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            indexed_constant_arithmetic_premises(&facts, &goal)
        });
        assert_eq!(selected.len(), 2, "{size} earlier clauses: {selected:?}");
        assert!(selected.contains(&lower));
        assert!(selected.contains(&upper));
        assert!(
            work <= size as usize * 4 + 256,
            "{size} clauses: {work} selection work"
        );
        let plan = plan_arithmetic(ArithmeticEngine::SignedInt32, &goal, &selected)
            .and_then(ArithmeticPlan::signed_int32)
            .unwrap();
        plan.check(&goal, &selected).unwrap();
    }
}
