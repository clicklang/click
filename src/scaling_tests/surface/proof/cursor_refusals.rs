#[test]
fn refusal_fact_listing_is_bounded() {
    let mut samples = Vec::new();
    for size in [32u64, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(710_000 + index)),
                true,
            ));
        }
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            listed_context_pure_facts(&[], Some(&context))
        });
        samples.push(work);
        assert!(!facts.is_empty());
    }
    eprintln!("refusal listing work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "ambient diagnostic scan: {samples:?}"
    );
}
