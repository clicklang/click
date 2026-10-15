// Scaling tests of `src/kernel/mutexes/invariant_interface.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn initialized_interface_exchange_scales_independently_of_resource_frame() {
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let (mut published, fact) = published();
        for index in 0..size {
            published.state.resources =
                published
                    .state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let before = published.state.mutex_ledger.as_ref().unwrap();
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let (held, guard) = published.acquire(&address(), &assumptions).unwrap();
                let released = held.release(guard, fact, &assumptions).unwrap();
                before
                    .check_protocol_state_since(released.state.mutex_ledger.as_ref().unwrap())
                    .unwrap();
                released
            })
        });
        assert!(Arc::ptr_eq(&binding(&published), &binding(&returned)));
        assert_eq!(returned.state.resources.facts().len(), size + 1);
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "interface transport scans unrelated resources: {samples:?}"
        );
    }
}

#[test]
fn use_interface_call_binding_scales_independently_of_resource_frame() {
    use crate::kernel::loans::mutex_calls::MutexUseCallTransfer;
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let (mut context, _) = published();
        for index in 0..size {
            context.state.resources =
                context
                    .state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Token {
                        name: format!("frame{index}"),
                        arguments: vec![].into(),
                    }));
        }
        let protocols = context.state.mutex_ledger.as_ref().unwrap();
        let owner = protocols.live_resource(&address()).unwrap();
        let loans = LoanLedger::new();
        let caller = loans.fresh_participant().unwrap();
        let helper = loans.fresh_participant().unwrap();
        let ((returned, work), persistent) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut transfer = MutexUseCallTransfer::prepare(
                    &loans,
                    caller,
                    helper,
                    &context.state.resources,
                    &owner,
                    &assumptions,
                )
                .unwrap();
                transfer.bind_interface(protocols).unwrap();
                transfer
                    .finish(
                        &transfer.ledger,
                        helper,
                        &transfer.callee_resources,
                        &[],
                        &assumptions,
                    )
                    .unwrap()
            })
        });
        assert_eq!(returned.caller_resources.facts().len(), size + 1);
        samples.push((work, persistent));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 2 + 1 && pair[1].1 <= pair[0].1 * 2 + 1,
            "use interface binding scans unrelated resources: {samples:?}"
        );
    }
}
