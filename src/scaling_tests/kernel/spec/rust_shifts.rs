#[test]
fn rust_shifts_are_fact_stable_and_do_not_scan_ambient_facts() {
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let x = Bitvector32Term::Variable(Variable(699_000));
        let n = Bitvector32Term::Variable(Variable(699_001));
        let mut base = PureFactContext::new();
        for index in 0..size {
            base = base.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(700_000 + index)),
                    1000u32.into(),
                ),
                true,
            );
        }
        let bound =
            ConditionTerm::unsigned_less_than(n.clone(), Bitvector32Term::UInt32Constant(8));
        let defined = base.clone().assume_condition(bound.clone(), true);
        let undefined = base.clone().assume_condition(bound.clone(), false);
        let impossible = defined.clone().assume_condition(bound, false);
        let written = SpecProposition::Comparison {
            left: SpecExpression::RustShiftLeft(
                Box::new(SpecExpression::Value(CValue::Int8(x))),
                Box::new(SpecExpression::Value(CValue::UInt32(n))),
            ),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(CValue::Int8(0u32.into())),
        };
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            [&base, &defined, &undefined, &impossible].map(|context| {
                crate::kernel::c_lower_spec_proposition_with_checked_obligations(
                    &CState::new(),
                    &written,
                    None,
                    context,
                )
                .unwrap()
            })
        });
        for actual in &lowered[1..] {
            assert_eq!(actual, &lowered[0]);
        }
        assert!(!lowered[0].2.is_empty());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
