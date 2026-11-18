use super::*;

fn split_credits(count: u32) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts((0..count).map(|_| {
        ResourceFact::own(Resource::Token {
            name: "credit".into(),
            arguments: vec![].into(),
        })
    }))
}

fn complete_partition(
    caller: &ExecutionState,
    function: &Arc<ProgramFunction>,
    receipt: &CheckedBoundaryResourceTransfer,
    outcome: StatementOutcome,
    facts: &PureFactContext,
) -> ExecutionState {
    let (result, obligations, _) = contract_exit_outcome_with_boundary_transfer(
        caller,
        function,
        &[],
        outcome,
        vec![],
        facts,
        &mut ExecutionBudget::beside_live_state(),
        ResourceTransitionPurpose::FunctionBoundary,
        Some(receipt),
    )
    .unwrap()
    .unwrap();
    assert!(obligations.is_empty());
    match result {
        FunctionOutcome::Return { state, .. } | FunctionOutcome::Throw { state, .. } => *state,
        other => panic!("completed body must retain its partition: {other:?}"),
    }
}

#[test]
fn ordinary_exceptional_and_fallthrough_exits_retain_split_occurrences() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let caller = ExecutionState::new().with_resource_context(split_credits(3));
    let function = Arc::new(
        program_function(ProgramType::Void, "retain_exit", vec![], program_skip())
            .with_int32_exceptional_outcome(),
    );
    let receipt = capture_checked_boundary_resource_transfer(
        &caller,
        function.clone(),
        &[],
        &facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    for outcome in [
        StatementOutcome::Return {
            value: ProgramValue::Void.into(),
            state: Box::new(caller.clone()),
        },
        StatementOutcome::Throw {
            value: int32(7).into(),
            state: Box::new(caller.clone()),
        },
        StatementOutcome::Normal(Box::new(caller.clone())),
    ] {
        let completed = complete_partition(&caller, &function, &receipt, outcome, &facts);
        assert!(
            Arc::ptr_eq(&caller.resources().storage, &completed.resources().storage),
            "completion must retain the actual partition and all occurrence identities"
        );
    }
}

#[test]
fn raw_observation_still_refuses_concretely_overlapping_descriptions() {
    let pointer = Address::symbolic(Variable(8_918_000));
    let raw =
        ResourceContext::new().unchecked_with_facts([(0u32, 4u32), (2, 6)].map(|(start, end)| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer.clone(),
                start.into(),
                end.into(),
                1,
            ))
        }));
    assert!(matches!(
        raw.observable_facts(&PureFactContext::new()),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/exit_partition_tests.rs");
}
