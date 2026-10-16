use super::*;
use crate::kernel::mutexes::helper_contracts::{HelperEffect, apply_call_effect};

#[test]
fn helper_summary_keeps_the_selected_sibling_share_and_checked_evidence() {
    let assumptions = PureFactContext::new();
    let mutex = crate::kernel::Pointer::symbolic(crate::kernel::Variable(865));
    let nominal = CResourceFact::own(CResource::MutexUse(crate::kernel::MutexUseIdentity {
        mutex: mutex.clone(),
        initialization: None,
        binding: None,
        protected: None,
    }));
    let resources = ResourceContext::new().unchecked_with_fact(nominal.clone());
    let support = resources
        .unique_owned_occurrence_for_fact(&nominal)
        .unwrap()
        .0;
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let (ledger, input) = ledger
        .borrowed_mutex_use_input(holder, support, mutex.clone())
        .unwrap();
    let (split, left, right) = ledger
        .split(input.usage.0.share, holder, holder, holder)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    let left = ledger
        .mutex_use_resource(
            MutexUseBinding(LoanAuthorityBinding {
                share: left,
                ..input.usage.0
            }),
            holder,
        )
        .unwrap();
    let right = ledger
        .mutex_use_resource(
            MutexUseBinding(LoanAuthorityBinding {
                share: right,
                ..input.usage.0
            }),
            holder,
        )
        .unwrap();
    let mut state = crate::kernel::CState::new();
    state.preserves_mutex_protocols = true;
    state.loan_ledger = Some(ledger.clone());
    state.loan_participant = Some(holder);
    state.resources = ResourceContext::new().unchecked_with_facts([left.clone(), right.clone()]);
    // Select the opposite of address lookup's candidate deliberately.
    let (selected, other) = if state.resources.mutex_use_candidate_at(&mutex) == Some(&left) {
        (right, left)
    } else {
        (left, right)
    };
    let (held, acquire_evidence, _) = apply_call_effect(
        &state,
        &selected,
        &selected,
        HelperEffect::Acquire,
        None,
        None,
        None,
        &[],
        &assumptions,
        &mut crate::kernel::ExecutionBudget::new(),
    )
    .unwrap();
    assert_eq!(
        acquire_evidence.recovered_ledger_for(&ledger, holder, false),
        held.loan_ledger
    );
    let guard = crate::kernel::mutexes::guard_resource(&held, &mutex, false).unwrap();
    assert!(
        apply_call_effect(
            &held,
            &other,
            &other,
            HelperEffect::Release,
            Some(&guard),
            None,
            None,
            &[],
            &assumptions,
            &mut crate::kernel::ExecutionBudget::new()
        )
        .is_err()
    );
    let (released, release_evidence, _) = apply_call_effect(
        &held,
        &selected,
        &selected,
        HelperEffect::Release,
        Some(&guard),
        None,
        None,
        &[],
        &assumptions,
        &mut crate::kernel::ExecutionBudget::new(),
    )
    .unwrap();
    let evidence = concat_checked_loan_evidence(&acquire_evidence, &release_evidence);
    assert!(evidence.is_valid());
    assert_eq!(
        evidence.recovered_ledger_for(&ledger, holder, false),
        released.loan_ledger
    );
    assert_eq!(released.resources.facts(), state.resources.facts());
    let (again, _, _) = apply_call_effect(
        &released,
        &selected,
        &selected,
        HelperEffect::Acquire,
        None,
        None,
        None,
        &[],
        &assumptions,
        &mut crate::kernel::ExecutionBudget::new(),
    )
    .unwrap();
    assert!(
        apply_call_effect(
            &again,
            &selected,
            &selected,
            HelperEffect::Release,
            Some(&guard),
            None,
            None,
            &[],
            &assumptions,
            &mut crate::kernel::ExecutionBudget::new()
        )
        .is_err()
    );
}
