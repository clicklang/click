use super::*;
use crate::kernel::int32;

#[test]
fn automatic_lifetime_event_rejects_active_local_loan_and_forged_retirement() {
    use crate::kernel::loans::{LoanLedger, plan_stable_view_transfer};
    use crate::kernel::prelude::CCheckedResourceFact;
    use crate::kernel::{CResourceSnapshot, CResourceTransferRole};
    let state = CState::new()
        .with_local("selected", int32(5))
        .with_memory(CMemory::new().with_block("local:selected", 4));
    let pointer = state.locals().slot("selected").unwrap().clone();
    let viewed = CResourceFact::view_memory(CMemoryRange::new(pointer.clone(), 0.into(), 1.into()));
    let ledger = LoanLedger::new();
    let caller = ledger.fresh_participant().unwrap();
    let callee = ledger.fresh_participant().unwrap();
    let assumptions = PureFactContext::new();
    let mut plan = plan_stable_view_transfer(
        &ResourceContext::new(),
        &[],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    plan.lend_local_views(
        state.memory(),
        &[CCheckedResourceFact {
            fact: viewed,
            role: CResourceTransferRole::Borrow,
            snapshot: CResourceSnapshot::Entry,
            clause_position: None,
            section_index: None,
            selected_mutex_source: None,
        }],
        &assumptions,
    )
    .unwrap();
    let state = state
        .with_loan_ledger(Some(plan.ledger.clone()))
        .with_loan_participant(Some(caller));
    let names = vec!["selected".to_string()];
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(core.record_automatic_lifetime_end(&state, &names).is_err());
    let forged = CheckedAutomaticLifetimeEnd {
        before_state: state.clone(),
        names,
        after_state: state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&pointer.block)),
    };
    assert!(forged.advance_checked(&state).is_none());
}

#[test]
fn automatic_lifetime_event_rejects_forged_mutex_storage_retirement() {
    let state = CState::new()
        .with_local("holder", int32(0))
        .with_memory(CMemory::new().with_block("local:holder", 48));
    let address = state.locals().slot("holder").unwrap().offset_by_bytes(8);
    let context = crate::kernel::mutexes::MutexContext::new(state)
        .initialize_empty(address.clone(), 40)
        .unwrap();
    let state = context.state();
    let names = vec!["holder".to_string()];
    let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
    assert!(matches!(
        core.record_automatic_lifetime_end(state, &names),
        Err(CRuntimeError::MutexStorageScopeEnd { .. })
    ));
    let forged = CheckedAutomaticLifetimeEnd {
        before_state: state.clone(),
        names: names.clone(),
        after_state: state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&address.block)),
    };
    assert!(forged.advance_checked(state).is_none());
    assert_eq!(core.reached_state(), state);
    let destroyed = context
        .destroy(&address, &PureFactContext::new())
        .unwrap()
        .into_state();
    let mut core = ExecutionProofCore::at_entry(destroyed.clone(), ExecutionFrontier::default());
    let after = core
        .record_automatic_lifetime_end(&destroyed, &names)
        .unwrap();
    let events = core.execution_evidence[0].to_vec();
    let CheckedExecutionEvent::AutomaticLifetimeEnd(event) = &events[0] else {
        panic!("missing scope event")
    };
    assert_eq!(event.advance_checked(&destroyed), Some(after));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/automatic_lifetime_tests.rs");
}
