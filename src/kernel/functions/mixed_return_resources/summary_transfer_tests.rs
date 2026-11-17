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
        .with_memory(Memory::new().with_block(pointer.block.clone(), 1024))
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

/// Model a body-certified identity function whose contract deliberately hides
/// the returned pointer's equality. Resource ownership is its only result rule.
pub(super) fn opaque_pointer_return_rule() -> VerifiedFunctionRule {
    let input = ResourceSpec::owned_memory(
        MemorySegment::new(variable("p"), int32_literal(0), int32_literal(1))
            .with_uninitialized(true),
    );
    let output = ResourceSpec::owned_memory(MemorySegment::new(
        ProgramExpression::Variable(BindingName::ContractResult),
        int32_literal(0),
        int32_literal(1),
    ))
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post);
    VerifiedFunctionRule {
        descent_completion: None,
        pointer_result: None,
        concrete_loop_exits: None,
        loop_semantics: LoopSemantics::Verify,
        checked_callees: None,
        applied_tactics: Default::default(),
        function: program_function(
            ProgramType::Int32Pointer,
            "opaque_pointer_return",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            program_return(variable("p")),
        )
        .with_resource_summary(vec![input], vec![output]),
    }
}

#[test]
fn verified_pointer_output_frames_without_a_geometric_recipe() {
    let _session = crate::kernel::VerificationSession::enter();
    let rule = opaque_pointer_return_rule();
    assert!(
        rule.function
            .contract_interface()
            .resource_transfer_rule
            .inputs_by_output
            .is_empty()
    );
    assert!(
        rule.function
            .contract_interface()
            .resource_transfer_rule
            .projected_inputs
            .is_empty()
    );
    let owner = |pointer, start: u32, end: u32| {
        ResourceFact::own_memory(MemoryRange::new(pointer, start.into(), end.into()))
    };
    let p = Pointer::symbolic(Variable(8_944_000));
    let held = owner(Pointer::symbolic(Variable(8_944_001)), 0, 1);
    let resources =
        ResourceContext::new().unchecked_with_facts([owner(p.clone(), 0, 1), held.clone()]);
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(p.block.clone(), 4))
        .with_resource_context(resources);
    let function = rule.function.clone();
    let env = ExecutionEnvironment::new().with_verified_function_rule(rule);
    let paths = execute_program_function_call_paths(
        &state,
        &function,
        &[ProgramExpression::Value(ProgramValue::pointer(p))],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&env),
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
        panic!("{paths:?}")
    };
    assert!(returned.resources().contains_exact_representation(&held));
    assert_eq!(returned.resources().flat_owned_memory_ranges().len(), 2);
    assert_eq!(state.resources().flat_owned_memory_ranges().len(), 2);
}

pub(super) fn partitioned_input_contract(count: u32, duplicate: bool) -> ProgramFunction {
    let mut children = (0..count)
        .map(|i| {
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("base"),
                int32_literal(i),
                int32_literal(i + 1),
            ))
        })
        .collect::<Vec<_>>();
    if duplicate {
        children.push(children[0].clone());
    }
    let definition = CompositeResourceDefinition::new(
        "parts",
        vec![program_parameter("base", ProgramType::Int32Pointer)],
        None,
        false,
        children,
        vec![],
    );
    let input = ResourceSpec::owned_memory(
        MemorySegment::new(variable("p"), int32_literal(0), int32_literal(count))
            .with_uninitialized(true),
    );
    let output = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "parts".into(),
        vec![variable("p")],
        vec![ProgramType::Int32Pointer],
    )
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post);
    program_function(
        ProgramType::Void,
        "partitioned_input",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_skip(),
    )
    .with_resource_summary(vec![input], vec![output])
    .with_composite_resource_definitions(vec![definition])
}

#[test]
fn constant_consumed_footprint_supplies_disjoint_fields_once() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(8_945_000));
    let facts = PureFactContext::new();
    let original = ResourceFact::own_memory(MemoryRange::new(p.clone(), 0u32.into(), 4u32.into()));
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(p.block.clone(), 16))
        .with_local("p", ProgramValue::pointer(p))
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(original.clone()),
        );
    for duplicate in [false, true] {
        let function = partitioned_input_contract(4, duplicate);
        let rule = &function.contract_interface().resource_transfer_rule;
        assert_eq!(rule.projected_inputs.len(), 4);
        assert!(!rule.projected_inputs.contains_key(&vec![0, 4]));
        let transfer = super::tests::prepare_mixed_scalar(&function, &state, &facts);
        let result = super::composite_transfer_tests::returned(
            &function,
            &state,
            &transfer,
            ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
            &facts,
        );
        assert_eq!(result.is_ok(), !duplicate, "duplicate={duplicate}");
        assert!(state.resources().contains_exact_representation(&original));
    }
}
