use super::*;

#[test]
fn late_conflict_uses_only_affected_predicate_parents() {
    let p = Pointer::symbolic(Variable(972_001));
    let q = Pointer::symbolic(Variable(972_002));
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut context = PureFactContext::new()
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(p.clone(), 8),
                true,
            ))
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(q.clone(), 8),
                false,
            ));
        for index in 0..count {
            context = context.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(Pointer::symbolic(Variable(980_000 + index)), 8),
                true,
            ));
        }
        let (conflicting, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.clone().assume_proposition(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(p.clone(), q.clone()),
                true,
            ))
        });
        assert!(conflicting.is_inconsistent());
        assert!(!context.is_inconsistent());
        assert!(work > 0);
        samples.push(work);
    }
    // The ambient predicate set quadruples each time. An indexed operand
    // merge follows the fixed affected parent set, allowing map-index costs.
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "{samples:?}"
    );
}
