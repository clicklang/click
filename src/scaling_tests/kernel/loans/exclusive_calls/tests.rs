// Scaling tests of `src/kernel/loans/exclusive_calls.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn exclusive_call_selected_transition_ignores_unrelated_scopes() {
    use super::super::super::tests::memory;
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let support = ResourceContext::new()
            .unchecked_with_fact(memory(0, 4, true))
            .unique_owned_occurrence_for_fact(&memory(0, 4, true))
            .unwrap()
            .0;
        for _ in 0..size {
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let (_, transition) = ledger
                .open_exclusive_call(caller, callee, vec![(memory(0, 4, true), support)])
                .unwrap();
            ledger = ledger.apply(&transition).unwrap();
        }
        let child = ledger.fresh_participant().unwrap();
        let ((), work) = crate::persistent::measure_persistent_work(|| {
            let (binding, enter) = ledger
                .open_exclusive_call(owner, child, vec![(memory(0, 4, true), support)])
                .unwrap();
            let entered = ledger.apply(&enter).unwrap();
            entered.validate_exclusive_call(&binding, child).unwrap();
            let leave = entered.return_exclusive_call(&binding, owner).unwrap();
            entered.apply(&leave).unwrap();
        });
        samples.push((size, work));
        assert!(
            work < 1200,
            "selected transition scanned unrelated scopes: {samples:?}"
        );
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 2 + 32,
            "selected lookup grew with ambient scopes: {samples:?}"
        );
    }
}
