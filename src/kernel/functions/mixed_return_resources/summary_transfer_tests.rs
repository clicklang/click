use super::*;
use crate::kernel::program_expression::{int32_literal, variable};

pub(super) fn symbolic_contract() -> ProgramFunction {
    let input = ResourceSpec::owned_memory(
        MemorySegment::new(variable("p"), int32_literal(0), variable("n")).with_uninitialized(true),
    );
    let output = input
        .clone()
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
    program_function(
        ProgramType::Void,
        "symbolic_transfer",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
            program_parameter("n", ProgramType::Int32),
        ],
        program_skip(),
    )
    .with_resource_summary(vec![input], vec![output])
}

pub(super) fn symbolic_state() -> (ExecutionState, PureFactContext, ResourceFact) {
    let pointer = Pointer::symbolic(Variable(8_940_000));
    let end = MachineTerm::Variable(Variable(8_940_001));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(1u32.into(), end.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(end.clone(), 16u32.into()),
            true,
        );
    let owner =
        ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0u32.into(), end.clone()));
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(SymbolicMemory::new().with_block(pointer.block.clone(), 1024))
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_local("q", ProgramValue::pointer(pointer))
        .with_local("n", ProgramValue::Int32(end))
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner.clone()),
        );
    (state, facts, owner)
}

#[test]
fn symbolic_summary_outputs_use_the_reserved_occurrence_and_keep_persistent_branches() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, owner) = symbolic_state();
    let function = symbolic_contract();
    let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
    let selected = transfer
        .consumed_cell_returns
        .get(0)
        .expect("symbolic transfer rule");
    assert_eq!(
        transfer.consumed_cell_returns.constructed.get(&0),
        Some(&owner)
    );
    for _ in 0..2 {
        let evaluated =
            super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
        assert_eq!(
            evaluated.occurrences[0].origin,
            ReturnOwnershipOrigin::ConsumedCell(selected)
        );
        let prepared = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
                &facts,
            )
            .unwrap();
        assert!(prepared.pending.facts().is_empty());
        let (returned, mappings) = prepared.finish(&facts).unwrap();
        assert_eq!(mappings[0].consumed_input, Some(selected.input));
        assert_eq!(
            returned.owned_fact_for_occurrence(mappings[0].destination),
            Some(&owner)
        );
    }
    assert_eq!(state.resources().facts(), &[owner]);
}

#[test]
fn summary_rule_is_single_use_and_raw_alias_outputs_still_need_separation_in_either_order() {
    for raw_first in [false, true] {
        for duplicate in [false, true] {
            let _session = crate::kernel::VerificationSession::enter();
            let (state, facts, _) = symbolic_state();
            let function = symbolic_contract();
            let input = function.resource_requires()[0].clone();
            let output = function.resource_ensures()[0].clone();
            let raw = if duplicate {
                output.clone()
            } else {
                ResourceSpec::owned_memory(
                    MemorySegment::new(variable("q"), int32_literal(0), variable("n"))
                        .with_uninitialized(true),
                )
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post)
            };
            let outputs = if raw_first {
                vec![raw, output]
            } else {
                vec![output, raw]
            };
            let function = function.with_resource_summary(vec![input], outputs);
            let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
            assert_eq!(transfer.consumed_cell_returns.constructed.len(), 1);
            let result = super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts)
                .and_then(|evaluated| {
                    evaluated
                        .restore_entry_borrows(
                            transfer.caller_resources_after_requirements.clone(),
                            ReturnResourceComposition::ApplyTransfers(
                                &transfer.consumed_cell_returns,
                            ),
                            &facts,
                        )
                        .and_then(|prepared| prepared.finish(&facts))
                        .map_err(resource_context_runtime_error)
                });
            assert!(result.is_err(), "duplicate authority accepted");
        }
    }
}

#[test]
fn raw_symbolic_description_cannot_use_a_contracts_transfer_rule() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, _) = symbolic_state();
    let function = symbolic_contract();
    let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
    let evaluated =
        super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let prepared = evaluated
        .restore_entry_borrows(
            state.resources().clone(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(prepared.restored.is_empty());
    assert!(prepared.finish(&facts).is_err());
}

#[test]
fn verified_summary_call_returns_a_symbolic_footprint_without_executing_the_body() {
    use crate::kernel::program_expression::pointer_value;
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, owner) = symbolic_state();
    let function = symbolic_contract();
    let environment =
        ExecutionEnvironment::new().with_verified_function_rule(VerifiedFunctionRule {
            descent_completion: None,
            pointer_result: None,
            function: function.clone(),
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let paths = execute_program_function_call_paths(
        &state,
        &function,
        &[
            pointer_value(owner.memory_own_range().unwrap().base().clone()),
            pointer_value(owner.memory_own_range().unwrap().base().clone()),
            variable("n"),
        ],
        &facts,
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let [
        FunctionPath {
            outcome: FunctionOutcome::Return {
                state: returned, ..
            },
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("summary call refused: {paths:?}")
    };
    assert!(returned.resources().contains_exact_representation(&owner));
    assert!(state.resources().contains_exact_representation(&owner));
}

#[test]
fn changing_the_contract_replaces_its_rule_and_does_not_infer_alias_or_guard_transfers() {
    let function = symbolic_contract();
    let retained_rule = function.contract_interface().resource_transfer_rule.clone();
    assert_eq!(retained_rule.inputs_by_output, BTreeMap::from([(0, 0)]));
    let input = function.resource_requires()[0].clone();
    let alias_output = ResourceSpec::owned_memory(MemorySegment::new(
        variable("q"),
        int32_literal(0),
        variable("n"),
    ))
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post);
    let changed = function
        .clone()
        .with_resource_summary(vec![input.clone()], vec![alias_output]);
    assert!(
        changed
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_output
            .is_empty()
    );
    let guarded = function.resource_ensures()[0]
        .clone()
        .with_guard(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(variable("n")),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(int32_literal(1)),
        });
    let changed = function.with_resource_summary(vec![input], vec![guarded]);
    assert!(
        changed
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_output
            .is_empty()
    );
    assert_eq!(retained_rule.inputs_by_output, BTreeMap::from([(0, 0)]));
}

#[test]
fn symbolic_summary_transfer_keeps_the_selected_slice_spelling_and_its_residual_frame() {
    let _session = crate::kernel::VerificationSession::enter();
    let (state, facts, original) = symbolic_state();
    let whole = ResourceFact::own_memory(MemoryRange::new(
        original.memory_own_range().unwrap().base().clone(),
        0u32.into(),
        32u32.into(),
    ));
    let expected = original;
    let state = state.with_resource_context(
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(whole),
    );
    let function = symbolic_contract();
    let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
    assert_eq!(
        transfer.caller_resources_after_requirements.facts().len(),
        1
    );
    assert_eq!(
        transfer.consumed_cell_returns.constructed.get(&0),
        Some(&expected)
    );
    let evaluated =
        super::tests::evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let (returned, mappings) = evaluated
        .restore_entry_borrows(
            transfer.caller_resources_after_requirements.clone(),
            ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    assert_eq!(
        returned.owned_fact_for_occurrence(mappings[0].destination),
        Some(&expected)
    );
    assert_eq!(returned.facts().len(), 2);
}
