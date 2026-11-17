use super::*;
#[test]
fn a_selected_return_backing_does_not_walk_other_call_loans() {
    let mut samples = Vec::new();
    for count in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let facts = PureFactContext::new();
        let mut index = ReturnLoanBackings::default();
        let mut selected = None;
        for item in 0..count {
            let (next, source) = source(
                &ledger,
                owner,
                reader,
                Pointer::symbolic(Variable(8_913_000 + u64::from(item))),
            );
            ledger = next;
            if item == 0 {
                selected = Some(source.clone());
            }
            index.add(source, &facts);
        }
        let selected = selected.unwrap();
        let head = ResourceFact::own_composite("returned".into(), vec![]);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast =
                crate::kernel::search::FastOperationScope::enter("selected returned source");
            assert_eq!(
                index
                    .select(&head, &selected.permission, &ledger, &facts)
                    .unwrap()
                    .support,
                selected.support
            );
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}
