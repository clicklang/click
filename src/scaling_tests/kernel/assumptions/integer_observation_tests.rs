// Scaling tests of native fact queries through exact Integer observations.

#[test]
fn native_observation_queries_use_the_selected_fact_index() {
    let samples = [8u64, 32, 128, 512].map(|size| {
        let condition =
            ConditionTerm::IntegerEqual(observe(MachineIntegerType::Int32, 880_001), constant(0));
        let (native, truth) = native_comparison_of_integer_observation(&condition, false).unwrap();
        let mut context = PureFactContext::new().assume_condition(native, truth);
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(word(890_000 + index), Bitvector32Term::Constant(7)),
                true,
            );
        }
        let (known, work) = crate::persistent::measure_persistent_work(|| {
            context.contains_known(&Proposition::ConditionIs(condition, false))
        });
        assert!(known);
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "an observation query scanned unrelated facts: {samples:?}"
    );
}
