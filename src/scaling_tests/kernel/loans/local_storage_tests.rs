// Scaling tests of `src/kernel/loans.rs` (module `local_storage_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn automatic_storage_retirement_lookup_scales_with_neither_loan_bucket() {
    let selected = SymbolicMemory::local_pointer("selected");
    let other = SymbolicMemory::local_pointer("other");
    for same_block in [false, true] {
        let samples = [4, 16, 64, 256].map(|count| {
            let mut ledger = BorrowLedger::new();
            let lender = ledger.fresh_participant().unwrap();
            let borrower = ledger.fresh_participant().unwrap();
            for index in 0..count {
                let base = if same_block {
                    selected.clone()
                } else {
                    SymbolicMemory::local_lifetime_pointer(index, "unrelated")
                };
                let range =
                    MemoryRange::new(base, 0u32.into(), MachineTerm::Variable(Variable(index)));
                let opening = lend_memory(&ledger, lender, borrower, range);
                ledger = ledger.apply(&opening.transition).unwrap();
            }
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                let size = &16u32.into();
                assert!(
                    ledger
                        .automatic_storage_retirement_refusal(&other.base, size)
                        .is_none()
                );
                ledger
                    .automatic_storage_retirement_refusal(&selected.base, size)
                    .is_some()
            });
            assert_eq!(found, same_block);
            work
        });
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 24),
            "{samples:?}"
        );
    }
}

#[test]
fn local_view_work_tracks_the_explicit_delta_not_ambient_local_storage() {
    let assumptions = PureFactContext::new();
    let mut fixed = Vec::new();
    let mut growing = Vec::new();
    for size in [8, 16, 32, 64] {
        let mut memory = SymbolicMemory::new();
        for index in 0..size {
            memory = memory.with_block(
                view(index, 1)
                    .fact
                    .memory_range()
                    .unwrap()
                    .base()
                    .base
                    .clone(),
                4,
            );
        }
        let mut one = plan();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            one.lend_local_views(&memory, &[view(0, 1)], &assumptions)
                .unwrap();
        });
        assert!(work > 0);
        fixed.push(work);
        let mut all = plan();
        let requirements = (0..size).map(|index| view(index, 1)).collect::<Vec<_>>();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            all.lend_local_views(&memory, &requirements, &assumptions)
                .unwrap();
            all.recover_stable_views(&assumptions, &BTreeMap::new(), &[])
                .unwrap();
        });
        growing.push(work);
    }
    assert!(
        fixed[3] <= fixed[0] * 2,
        "local loan scans ambient storage: {fixed:?}"
    );
    for pair in growing.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "local loan work exceeds its explicit delta: {growing:?}"
        );
    }
}

#[test]
fn local_loan_admission_tracks_selected_backing_with_live_loans_and_aliases() {
    let requirement = view(0, 1);
    let local = requirement.fact.memory_range().unwrap().base().clone();
    let memory = SymbolicMemory::new().with_block(local.base.clone(), 4);
    for worker in [false, true] {
        let samples = [4, 16, 64].map(|count| {
            let mut ledger = BorrowLedger::new();
            let caller = ledger.fresh_participant().unwrap();
            let callee = ledger.fresh_participant().unwrap();
            let mut assumptions = PureFactContext::new();
            for index in 0..count {
                let unrelated = SymbolicMemory::local_lifetime_pointer(index, "unrelated");
                let range = MemoryRange::new(unrelated.clone(), 0u32.into(), 1u32.into());
                let opening = lend_memory(&ledger, caller, callee, range);
                ledger = ledger.apply(&opening.transition).unwrap();
                assumptions = assumptions.assume_condition(
                    crate::kernel::ConditionTerm::address_equal(
                        unrelated,
                        Address::symbolic(Variable(99_000 + index)),
                    ),
                    true,
                );
            }
            let mut plan = plan_stable_view_transfer(
                &ResourceContext::new(),
                &[],
                &assumptions,
                &ledger,
                caller,
                callee,
            )
            .unwrap();
            let existing = BTreeMap::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                plan.lend_local_views_with_worker_shares(
                    &memory,
                    std::slice::from_ref(&requirement),
                    &assumptions,
                    worker.then_some(&existing),
                )
                .unwrap();
                plan.recheck_entry(&ledger).unwrap();
            });
            assert_eq!(plan.stable_views.len(), 1);
            work
        });
        assert!(samples[2] <= samples[0] + 48, "{worker}: {samples:?}");
    }
}
