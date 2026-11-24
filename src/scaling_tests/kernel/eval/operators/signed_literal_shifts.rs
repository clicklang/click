use super::*;

#[test]
fn signed_literal_shift_headroom_uses_the_exact_count_bound() {
    let count = MachineTerm::var(Variable(974_001));
    let one = MachineTerm::constant(1);
    for related in [false, true] {
        let samples = [4, 16, 64].map(|size| {
            let mut facts = PureFactContext::new().assume_condition(
                ConditionTerm::signed_less_than(count.clone(), MachineTerm::constant(31)),
                true,
            );
            for index in 0..size {
                let value = if related {
                    count.clone()
                } else {
                    MachineTerm::var(Variable(974_100 + u64::from(index)))
                };
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(value, MachineTerm::constant(100 + index)),
                    true,
                );
            }
            let (fits, work) = crate::instrumentation::measure_deterministic_work(|| {
                literal_signed_shift_fits(
                    MachineIntegerType::Int32,
                    &one,
                    &count,
                    false,
                    &facts,
                    &ExecutionFacts::new(),
                )
            });
            assert!(fits);
            work
        });
        assert_eq!(samples, [samples[0]; 3], "{related}: {samples:?}");
    }
}
