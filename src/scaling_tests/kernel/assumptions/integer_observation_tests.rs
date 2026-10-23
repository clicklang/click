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

#[test]
fn filing_an_integer_reading_through_an_operation_visits_only_its_own_bounds() {
    // Filing the Integer reading of a native guard, and the second bound of
    // a signed definedness fact, looks up only those facts' own bounds,
    // however many unrelated facts the context holds.
    let samples = [8u64, 32, 128, 512].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::IntegerLessEqual(
                    difference(900_000 + index, 900_001 + index),
                    constant(7),
                ),
                true,
            );
        }
        let guard = ConditionTerm::IntegerLessEqual(
            observe(MachineIntegerType::UInt32, 1),
            uint32_difference_from(4_294_967_295, 2),
        );
        let upper = ConditionTerm::IntegerLessEqual(difference(3, 4), constant(2_147_483_647));
        let lower = ConditionTerm::IntegerGreaterEqual(difference(3, 4), constant(-2_147_483_648));
        let context = context.assume_condition(upper, true);
        let (context, work) = crate::persistent::measure_persistent_work(|| {
            context
                .assume_condition(guard, true)
                .assume_condition(lower, true)
        });
        assert_eq!(context.decide(&uint32_guard(u32::MAX, 1, 2)), Some(true));
        assert_eq!(
            context.decide(&ConditionTerm::signed_subtract_overflows(word(3), word(4))),
            Some(false)
        );
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "filing an operation reading scanned unrelated facts: {samples:?}"
    );
}

#[test]
fn filing_a_quantified_integer_antecedent_visits_only_its_own_bounds() {
    // Filing a quantified fact whose antecedent reads through an in-range
    // sum looks up only that sum's range bound, however many unrelated facts
    // the context holds.
    let samples = [8u64, 32, 128, 512].map(|size| {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::IntegerLessEqual(
                    difference(900_000 + index, 900_001 + index),
                    constant(7),
                ),
                true,
            );
        }
        let sum: SharedIntegerTerm =
            IntegerTerm::Add(observe(MachineIntegerType::UInt64, 831), constant(1)).into();
        let reading =
            ConditionTerm::IntegerLessThan(observe(MachineIntegerType::UInt64, 830), sum.clone());
        let (native, truth, _) = native_comparison_through_integer_operations(&reading, true).unwrap();
        let context = context.assume_condition(ConditionTerm::IntegerLessEqual(sum, uint64_max()), true);
        let (context, work) = crate::persistent::measure_persistent_work(|| {
            context.assume_proposition(quantified_over_k(Proposition::ConditionIs(reading, true)))
        });
        assert!(context.contains_known(&quantified_over_k(Proposition::ConditionIs(native, truth))));
        work
    });
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 32),
        "filing a quantified antecedent's reading scanned unrelated facts: {samples:?}"
    );
}
