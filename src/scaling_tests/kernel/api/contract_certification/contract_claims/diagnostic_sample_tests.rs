// A fixed-size refusal must not visit every fact just to select its sample.
#[test]
fn contract_refusal_sample_ignores_unprinted_facts() {
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(650_000 + index)),
                    Bitvector32Term::Constant(1000),
                ),
                true,
            );
        }
        let all = context.pure_facts();
        let expected = all[..8]
            .iter()
            .chain(all[all.len() - 24..].iter())
            .cloned()
            .collect::<Vec<_>>();
        let obligation = ProofObligation::verification_condition(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                let failure = unproved_contract_path_condition(
                    "missing premise".into(),
                    &obligation,
                    &context,
                );
                assert_eq!(failure.available_count, all.len());
                assert_eq!(failure.available, expected);
            }
        });
        samples.push((size, work));
    }
    eprintln!("contract refusal sampling work: {samples:?}");
    assert!(samples[2].1 <= samples[0].1 * 2, "{samples:?}");
}
