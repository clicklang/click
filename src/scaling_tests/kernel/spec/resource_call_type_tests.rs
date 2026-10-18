use super::*;

#[test]
fn selected_call_domain_recovery_ignores_unrelated_context() {
    let _session = VerificationSession::enter();
    let source = clause(value(945_004));
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: vec![Term::CValue(value(946_000 + index))],
            });
        }
        let (paths, work) =
            crate::instrumentation::measure_deterministic_work(|| lower(&source, &context, true));
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].facts.len(), 1);
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2),
        "{samples:?}"
    );
}
