use super::direct_loop_guard::{
    normalize_direct_loop_guards, prepare_direct_loop_guard, select_direct_loop_guards,
};
use super::*;
use crate::kernel::*;

fn address(index: usize) -> Address {
    Address {
        base: format!("direct-loop-{index}").into(),
        offset: AddressOffset::Constant(0),
    }
}
fn spec() -> ResourceSpec {
    ResourceSpec::new(
        ResourceTerm::MutexGuard {
            mutex: Box::new(crate::kernel::program_expression::variable("mutex")),
            state_source: ResourceStateSource::Current,
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap()
    .with_guard(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            "flag",
        )),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(int32(1)),
    })
}
fn entry() -> ExecutionState {
    MutexContext::new(
        ExecutionState::new()
            .with_local("mutex", ProgramValue::pointer(address(0)))
            .with_local("flag", int32(0)),
    )
    .initialize_empty(address(0), 40)
    .unwrap()
    .state
}
fn head(entry: &ExecutionState, identity: u64) -> ExecutionState {
    let (state, _, _) = prepare_direct_loop_guard(
        entry,
        entry,
        &spec(),
        InstanceId::from_variable(Variable(identity)),
        &PureFactContext::new(),
    )
    .unwrap();
    select_direct_loop_guards(&state, vec![address(0)])
}
fn carrier(state: &ExecutionState) -> Arc<ConditionalMutexGuard> {
    state
        .mutex_ledger
        .as_ref()
        .unwrap()
        .storage
        .direct_loop_carriers
        .get(&address(0))
        .unwrap()
        .head
        .clone()
}

#[test]
fn direct_loop_guard_requires_real_entry_custody() {
    let state = entry().with_local("flag", int32(1));
    assert!(
        prepare_direct_loop_guard(
            &state,
            &state,
            &spec(),
            InstanceId::from_variable(Variable(700)),
            &PureFactContext::new()
        )
        .unwrap_err()
        .contains("mutex_guard")
    );
}
#[test]
fn direct_loop_guard_rechecks_changed_discriminator_without_mutex_operations() {
    let top = head(&entry(), 701);
    let next = top.clone().with_local("flag", int32(1));
    assert!(
        normalize_direct_loop_guards(&top, &next, &PureFactContext::new())
            .unwrap_err()
            .contains("mutex_guard")
    );
}
#[test]
fn direct_loop_guard_metadata_does_not_replace_owned_carrier() {
    let locked = MutexContext::new(entry())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let top = head(&locked.state().clone().with_local("flag", int32(1)), 702);
    let mut missing = top.clone();
    let carrier = missing
        .mutex_ledger
        .as_ref()
        .unwrap()
        .storage
        .direct_loop_carriers
        .get(&address(0))
        .unwrap();
    let owned = super::direct_loop_guard::fact(carrier);
    missing.resources = missing
        .resources
        .without_fact_incrementally(&owned, &PureFactContext::new())
        .unwrap();
    let locked = MutexContext::new(missing.clone().with_local("flag", int32(1)));
    assert!(
        locked
            .release_current(&address(0), &PureFactContext::new())
            .is_err()
    );
}
#[test]
fn direct_loop_guard_checked_open_allows_a_subsequent_loop() {
    let first = head(&entry(), 703);
    let locked = MutexContext::new(first)
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let unlocked = locked
        .release_current(&address(0), &PureFactContext::new())
        .unwrap();
    let second = head(unlocked.state(), 704);
    assert_eq!(
        carrier(&second).identity,
        InstanceId::from_variable(Variable(704))
    );
}
#[test]
fn direct_loop_guard_rejects_changed_mutex_address() {
    let entry = entry();
    let changed = entry
        .clone()
        .with_local("mutex", ProgramValue::pointer(address(1)));
    assert!(
        prepare_direct_loop_guard(
            &entry,
            &changed,
            &spec(),
            InstanceId::from_variable(Variable(705)),
            &PureFactContext::new()
        )
        .is_err()
    );
}

#[test]
fn direct_loop_guard_empty_carrier_allows_a_subsequent_loop() {
    let first = head(&entry(), 707);
    let second = head(&first, 708);
    assert_eq!(
        carrier(&second).identity,
        InstanceId::from_variable(Variable(708))
    );
}

#[test]
fn direct_loop_guard_is_typed_and_affine_even_when_empty() {
    let top = head(&entry(), 710);
    assert!(
        top.resources
            .owned_instance(InstanceId::from_variable(Variable(710)))
            .is_none()
    );
    let owned = ResourceFact::own(Resource::ConditionalMutexGuard(carrier(&top)));
    assert!(
        top.resources
            .unique_owned_occurrence_for_fact(&owned)
            .is_some()
    );
    assert!(
        top.resources
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                [owned.clone()],
                &PureFactContext::new()
            )
            .is_err()
    );
    let mut different = (*carrier(&top)).clone();
    different.held = ConditionTerm::Constant(true).into();
    assert!(
        top.resources
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                [ResourceFact::own(Resource::ConditionalMutexGuard(
                    Arc::new(different)
                ))],
                &PureFactContext::new()
            )
            .is_err()
    );
    assert!(
        ResourceContext::new()
            .try_compose_into_valid_context_delaying_normalization(
                [ResourceFact::View(owned.resource().clone())],
                &PureFactContext::new()
            )
            .is_err()
    );
}

#[test]
fn direct_loop_guard_has_the_existing_conditional_clause_spelling() {
    let top = head(&entry(), 713);
    let owned = ResourceFact::own(Resource::ConditionalMutexGuard(carrier(&top)));
    let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::with_state(
        crate::surface::ParameterBinding::default(),
        &top,
    );
    let source = crate::surface::proof_diagnostics::render::render_resource_fact_spelled(
        &owned,
        &mut labels,
    );
    assert!(source.starts_with("if "), "{source}");
    assert!(source.contains("owns mutex_guard("), "{source}");
    let sidecar =
        format!("void example(int32* mutex) {{ ensures true; }} by {{ loop {{ {source} }} }}");
    crate::surface::parse(&sidecar)
        .expect("the typed carrier uses the existing conditional clause syntax");
    assert!(
        !source.contains("$conditional") && !source.contains("active"),
        "{source}"
    );
}

#[test]
fn direct_loop_guard_backedge_consumes_the_current_acquisition() {
    let top = head(&entry(), 711);
    let locked = MutexContext::new(top.clone())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let next = locked.state().clone().with_local("flag", int32(1));
    let current = next
        .mutex_ledger
        .as_ref()
        .unwrap()
        .guard_resource(&address(0))
        .unwrap();
    let (closed, checked) =
        normalize_direct_loop_guards(&top, &next, &PureFactContext::new()).unwrap();
    assert_eq!(checked, vec![address(0)]);
    assert!(
        closed
            .resources
            .unique_owned_occurrence_for_fact(&current)
            .is_none()
    );
    assert!(
        closed
            .resources
            .unique_owned_occurrence_for_fact(&ResourceFact::own(Resource::ConditionalMutexGuard(
                carrier(&top)
            )))
            .is_some()
    );
    let missing = next.clone().with_resource_context(
        next.resources
            .clone()
            .without_fact_incrementally(&current, &PureFactContext::new())
            .unwrap(),
    );
    assert!(normalize_direct_loop_guards(&top, &missing, &PureFactContext::new()).is_err());
}

#[test]
fn direct_loop_guard_open_refuses_a_stale_acquisition() {
    let locked = MutexContext::new(entry())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let mut top = head(&locked.state().clone().with_local("flag", int32(1)), 712);
    let ledger = top.mutex_ledger.as_ref().unwrap();
    let MutexEntry::ConditionalLoop {
        initialization,
        epoch,
        held,
    } = ledger.get(&address(0)).unwrap()
    else {
        panic!("conditional protocol")
    };
    top.mutex_ledger = Some(ledger.with_inserted(
        address(0),
        MutexEntry::ConditionalLoop {
            initialization: *initialization,
            epoch: epoch + 1,
            held: held.clone(),
        },
    ));
    assert!(
        MutexContext::new(top)
            .open_direct_loop_guard(&address(0), &PureFactContext::new())
            .is_err()
    );
}

#[test]
fn direct_loop_guard_open_refuses_a_new_initialization_at_the_same_address() {
    let mut top = head(&entry(), 714);
    let ledger = top.mutex_ledger.as_ref().unwrap();
    let MutexEntry::ConditionalLoop {
        initialization,
        epoch,
        held,
    } = ledger.get(&address(0)).unwrap()
    else {
        panic!("conditional protocol")
    };
    top.mutex_ledger = Some(ledger.with_inserted(
        address(0),
        MutexEntry::ConditionalLoop {
            initialization: MutexInitialization(
                MutexInitializationId::fresh().unwrap(),
                initialization.1,
            ),
            epoch: *epoch,
            held: held.clone(),
        },
    ));
    assert!(
        MutexContext::new(top)
            .open_direct_loop_guard(&address(0), &PureFactContext::new())
            .is_err()
    );
}

#[test]
fn direct_loop_guard_keeps_negated_conditions_as_boolean_terms() {
    let locked = MutexContext::new(entry())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let condition = spec().guard().unwrap().clone();
    let spec = spec().with_guard(SpecProposition::Not(Box::new(condition)));
    let (head, _, _) = prepare_direct_loop_guard(
        locked.state(),
        locked.state(),
        &spec,
        InstanceId::from_variable(Variable(715)),
        &PureFactContext::new(),
    )
    .unwrap();
    assert!(matches!(
        carrier(&head).condition(),
        ConditionTerm::BoolEqual(..)
    ));
    let opened = MutexContext::new(head)
        .release_current(&address(0), &PureFactContext::new())
        .unwrap();
    assert!(
        opened
            .state()
            .mutex_ledger
            .as_ref()
            .unwrap()
            .guard_resource(&address(0))
            .is_none()
    );
}

#[test]
fn direct_loop_guard_transfer_rejects_an_existing_guard_atom() {
    let locked = MutexContext::new(entry())
        .acquire_current(&address(0), &PureFactContext::new())
        .unwrap();
    let top = head(&locked.state().clone().with_local("flag", int32(1)), 716);
    let mut duplicate = top.clone();
    duplicate.resources =
        duplicate
            .resources
            .unchecked_with_fact(ResourceFact::own(Resource::MutexGuard(
                carrier(&top).guard.clone(),
            )));
    assert!(
        MutexContext::new(duplicate)
            .open_direct_loop_guard(&address(0), &PureFactContext::new())
            .is_err()
    );
}

#[test]
fn direct_loop_guard_transfer_rejects_an_existing_conditional_identity() {
    let top = head(&entry(), 717);
    let mut changed = (*carrier(&top)).clone();
    changed.held = ConditionTerm::Constant(true).into();
    assert!(
        top.resources
            .clone()
            .insert_transferred_conditional_guard(Arc::new(changed))
            .is_err()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/mutexes/direct_loop_guard_tests.rs");
}

#[test]
fn conditional_guard_and_ledger_retain_one_logical_condition_root() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = head(&entry(), 10993641);
    let guard = carrier(&state);
    let root = guard.held.root().expect("checked condition stays common");
    let Some(MutexEntry::ConditionalLoop { held, .. }) =
        state.mutex_ledger.as_ref().unwrap().get(&address(0))
    else {
        panic!("conditional ledger");
    };
    assert_eq!(held.root(), Some(root));
}
