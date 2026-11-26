use super::*;
use crate::kernel::mutexes::MutexContext;

fn address(index: usize) -> Address {
    Address::new(
        format!("typed-held-{index}").into(),
        AddressOffset::constant(0),
    )
}
fn observe(state: &ExecutionState, assumptions: &PureFactContext) -> SpecPropositionPath {
    let spec = SpecProposition::MutexHeld(Box::new(SpecExpression::Value(ProgramValue::pointer(
        address(0),
    ))));
    let mut paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        &spec,
        None,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap()
}

#[test]
fn held_observes_protocol_without_creating_ownership() {
    let initial = MutexContext::new(ExecutionState::new())
        .initialize_empty(address(0), 40)
        .unwrap();
    assert_eq!(
        observe(initial.state(), &PureFactContext::new()).proposition,
        Proposition::condition_is(OldConditionTerm::Constant(false), true)
    );
    let locked = initial
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let mut missing = locked.state().clone();
    let guard = missing
        .mutex_ledger
        .as_ref()
        .unwrap()
        .guard_resource(&address(0))
        .unwrap();
    missing.resources = missing
        .resources
        .without_fact_incrementally(&guard, &PureFactContext::new())
        .unwrap();
    let path = observe(&missing, &PureFactContext::new());
    assert_eq!(
        path.proposition,
        Proposition::condition_is(OldConditionTerm::Constant(true), true)
    );
    assert!(path.obligations.is_empty());
    assert!(
        MutexContext::new(missing)
            .release_current(&address(0), &PureFactContext::new())
            .is_err()
    );
}

#[test]
fn held_is_a_resource_state_dependency() {
    let spec = SpecProposition::MutexHeld(Box::new(SpecExpression::Value(ProgramValue::pointer(
        address(0),
    ))));
    assert!(predicate_dependencies::observes_resource_state(&spec));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/mutex_held_tests.rs");
}
