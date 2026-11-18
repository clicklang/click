use super::*;

fn owner(pointer: Address, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(pointer, start.into(), end.into()))
}

#[test]
fn mixed_composition_restores_symbolic_borrows_and_keeps_emitted_occurrence_order() {
    let facts = PureFactContext::new();
    let pointer = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(8_810_000)),
    };
    let borrow = owner(pointer.clone(), 0, 1);
    let produced = owner(Address::symbolic(Variable(8_810_001)), 0, 1);
    let parent =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(pointer, 4, 5));
    parent.synchronize_memory_equalities(&facts);
    for produced_first in [false, true] {
        let (outputs, entry_borrows) = if produced_first {
            (vec![produced.clone(), borrow.clone()], vec![false, true])
        } else {
            (vec![borrow.clone(), produced.clone()], vec![true, false])
        };
        let evaluated = outputs.iter().cloned().zip(entry_borrows).fold(
            EvaluatedReturnResources::new(&facts),
            |evaluated, (fact, entry_borrow)| {
                evaluated
                    .admit(
                        fact,
                        if entry_borrow {
                            ReturnOwnershipOrigin::EntryBorrow
                        } else {
                            ReturnOwnershipOrigin::Description
                        },
                        &facts,
                    )
                    .unwrap()
            },
        );
        let _operation =
            crate::kernel::search::FastOperationScope::enter("mixed return composition");
        let prepared = evaluated
            .restore_entry_borrows(
                parent.clone(),
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap();
        assert!(prepared.frame.contains_exact_representation(&borrow));
        assert_eq!(prepared.pending.facts(), std::slice::from_ref(&produced));
        let (context, inserted) = prepared.finish(&facts).unwrap();
        assert_eq!(context.facts().len(), 3);
        assert_eq!(inserted.len(), outputs.len());
        for ((transfer, source), fact) in inserted.iter().zip(&evaluated.occurrences).zip(&outputs)
        {
            assert_eq!(transfer.source, source.source);
            assert_eq!(
                evaluated
                    .resources
                    .owned_fact_for_occurrence(transfer.source),
                Some(fact)
            );
            assert_eq!(
                context.owned_fact_for_occurrence(transfer.destination),
                Some(fact)
            );
        }
        assert_eq!(parent.facts().len(), 1);
    }
}

#[test]
fn raw_description_mode_never_authorizes_restoration_from_a_role_marker() {
    let facts = PureFactContext::new();
    let borrow = owner(Address::symbolic(Variable(8_810_010)), 0, 1);
    let parent = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(borrow.clone());
    parent.synchronize_memory_equalities(&facts);
    let descriptions = EvaluatedReturnResources::new(&facts)
        .admit(borrow, ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap();
    let prepared = descriptions
        .restore_entry_borrows(
            parent,
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(prepared.restored.is_empty());
    assert!(matches!(
        prepared.finish(&facts),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
}

#[test]
fn equal_return_descriptions_keep_distinct_transfers_and_projection_lifetimes() {
    let facts = PureFactContext::new();
    let ticket = ResourceFact::own_token("returned_ticket".into(), vec![]);
    for borrowed_first in [false, true] {
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                ticket.clone(),
                if borrowed_first {
                    ReturnOwnershipOrigin::EntryBorrow
                } else {
                    ReturnOwnershipOrigin::Description
                },
                &facts,
            )
            .unwrap()
            .admit(
                ticket.clone(),
                if !borrowed_first {
                    ReturnOwnershipOrigin::EntryBorrow
                } else {
                    ReturnOwnershipOrigin::Description
                },
                &facts,
            )
            .unwrap();
        let sources = evaluated
            .occurrences
            .iter()
            .map(|entry| entry.source)
            .collect::<Vec<_>>();
        assert_ne!(sources[0], sources[1]);
        for _ in 0..2 {
            let prepared = evaluated
                .restore_entry_borrows(
                    ResourceContext::new_with_equalities(&facts),
                    ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                    &facts,
                )
                .unwrap();
            let restored = prepared.restored.values().next().unwrap().destination;
            let (mut destination, transfers) = prepared.finish(&facts).unwrap();
            assert_eq!(transfers[0].source, sources[0]);
            assert_eq!(transfers[1].source, sources[1]);
            assert_ne!(transfers[0].destination, transfers[1].destination);
            assert_eq!(
                transfers[usize::from(!borrowed_first)].destination,
                restored
            );
            let state = ExecutionState::new();
            let projected = project_return_resource_cores(
                &evaluated.resources,
                &transfers,
                &ConstructedReturnBodies::default(),
                &facts,
                &destination,
            );
            assert_eq!(projected.len(), 2);
            let mut views = Vec::new();
            for (projection, transfer) in projected.into_iter().zip(&transfers) {
                assert_eq!(projection.destination, transfer.destination);
                assert_eq!(projection.support, ticket);
                assert_eq!(projection.projected.len(), 1);
                let (next, inserted) = destination
                    .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                        projection.destination,
                        &projection.support,
                        projection.projected,
                        state.memory(),
                    );
                destination = next;
                views.push(inserted[0].1);
            }
            for removed in 0..2 {
                let kept = 1 - removed;
                let child = destination
                    .clone()
                    .without_exact_representation_for_occurrence(transfers[removed].destination)
                    .unwrap();
                assert!(
                    child
                        .owned_fact_for_occurrence(transfers[removed].destination)
                        .is_none()
                );
                assert!(child.view_fact_for_occurrence(views[removed]).is_none());
                assert_eq!(
                    child.owned_fact_for_occurrence(transfers[kept].destination),
                    Some(&ticket)
                );
                assert!(child.view_fact_for_occurrence(views[kept]).is_some());
                assert!(
                    destination
                        .view_fact_for_occurrence(views[removed])
                        .is_some()
                );
            }
        }
        assert_eq!(evaluated.resources.facts().len(), 2);
    }
}

pub(super) fn scalar_transfer_contract(output: MemorySegment) -> ProgramFunction {
    use crate::kernel::program_expression::{int32_literal, variable};
    program_function(
        ProgramType::Void,
        "scalar_transfer",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_skip(),
    )
    .with_resource_summary(
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            ))
            .with_role(ResourceTransferRole::Consume),
        ],
        vec![
            ResourceSpec::owned_memory(output)
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post),
        ],
    )
}

pub(super) fn prepare_scalar_transfer(
    function: &ProgramFunction,
    pointer: Address,
    caller: ResourceContext,
    facts: &PureFactContext,
) -> FunctionResourceTransfer {
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 1024))
        .with_local("p", ProgramValue::pointer(pointer))
        .with_resource_context(caller);
    prepare_contract_resource_transfer(
        &state,
        &state,
        function.name(),
        function.contract_interface(),
        facts,
        &mut ExecutionBudget::beside_live_state(),
        false,
        ResourceTransitionPurpose::CallSite,
    )
    .unwrap()
    .unwrap()
}

#[test]
fn consumed_scalar_transfer_retains_entry_and_emitted_occurrences_on_branches() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_860_000));
    let cell = owner(pointer.clone(), 0, 1);
    let held = owner(pointer.clone(), 1, 2);
    let caller = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts([cell.clone(), held.clone()]);
    let function = scalar_transfer_contract(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ));
    let transfer = prepare_scalar_transfer(&function, pointer, caller.clone(), &facts);
    let selected = transfer
        .consumed_cell_returns
        .get(0)
        .expect("explicit scalar transfer");
    assert_eq!(
        caller.owned_fact_for_occurrence(selected.input),
        Some(&cell)
    );
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            cell.clone(),
            ReturnOwnershipOrigin::ConsumedCell(selected),
            &facts,
        )
        .unwrap();
    for _ in 0..2 {
        let (result, mapping) = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        assert_eq!(mapping.len(), 1);
        assert_eq!(mapping[0].consumed_input, Some(selected.input));
        assert_eq!(mapping[0].source, evaluated.occurrences[0].source);
        assert_eq!(
            result.owned_fact_for_occurrence(mapping[0].destination),
            Some(&cell)
        );
        let remaining = result
            .without_exact_representation_for_occurrence(mapping[0].destination)
            .unwrap();
        assert_eq!(remaining.facts(), std::slice::from_ref(&held));
    }
    assert_eq!(caller.facts().len(), 2);
    assert_eq!(
        transfer.caller_resources_after_requirements.facts(),
        &[held]
    );
}

#[test]
fn changed_scalar_output_keeps_description_validation_and_rejects_overlap() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_860_010));
    for (start, end) in [(1, 2), (0, 2)] {
        let caller = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts([owner(pointer.clone(), 0, 1), owner(pointer.clone(), 1, 2)]);
        let function = scalar_transfer_contract(MemorySegment::new(
            variable("p"),
            int32_literal(start),
            int32_literal(end),
        ));
        let transfer = prepare_scalar_transfer(&function, pointer.clone(), caller, &facts);
        assert!(transfer.consumed_cell_returns.get(0).is_none());
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                owner(pointer.clone(), start, end),
                ReturnOwnershipOrigin::Description,
                &facts,
            )
            .unwrap();
        assert!(
            evaluated
                .restore_entry_borrows(
                    transfer.caller_resources_after_requirements,
                    ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                    &facts,
                )
                .unwrap()
                .finish(&facts)
                .is_err()
        );
    }
}

#[test]
fn verified_scalar_call_uses_transfer_and_raw_return_descriptions_still_validate() {
    use crate::kernel::program_expression::{int32_literal, pointer_value, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_860_020));
    let function = scalar_transfer_contract(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ));
    let cell = owner(pointer.clone(), 0, 1);
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 8))
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(cell.clone()),
        );
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
        &[pointer_value(pointer)],
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
        panic!("scalar call failed: {paths:?}")
    };
    assert!(returned.resources().satisfies_fact(&cell, &facts));
    let raw = EvaluatedReturnResources::new(&facts)
        .admit(cell, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    assert!(
        raw.restore_entry_borrows(
            state.resources().clone(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .is_err()
    );
}

#[test]
fn consumed_scalar_transfer_preserves_output_spelling_and_partial_residual() {
    use crate::kernel::program_expression::{int32_literal, variable};
    for alias in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let original = Address::symbolic(Variable(8_860_030));
        let returned = if alias {
            Address::symbolic(Variable(8_860_031))
        } else {
            original.clone()
        };
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::address_equal(original.clone(), returned.clone()),
            true,
        );
        let caller =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(original, 0, 2));
        let function = scalar_transfer_contract(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ));
        let transfer = prepare_scalar_transfer(&function, returned.clone(), caller, &facts);
        let selected = transfer
            .consumed_cell_returns
            .get(0)
            .expect("selected flat slice");
        let cell = owner(returned.clone(), 0, 1);
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                cell.clone(),
                ReturnOwnershipOrigin::ConsumedCell(selected),
                &facts,
            )
            .unwrap();
        let (result, mapping) = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        assert_eq!(
            result.owned_fact_for_occurrence(mapping[0].destination),
            Some(&cell)
        );
        assert!(result.satisfies_fact(&owner(returned, 1, 2), &facts));
        assert_eq!(result.facts().len(), 2);
    }
}

#[test]
fn consumed_scalar_transfer_is_single_use_and_declines_entry_borrows() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::symbolic(Variable(8_860_040));
    let facts = PureFactContext::new();
    let caller = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
        pointer.clone(),
        0,
        1,
    ));
    let function = scalar_transfer_contract(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ));
    let input = function.contract_interface().resource_requires()[0].clone();
    let output = function.contract_interface().resource_ensures()[0].clone();
    let duplicate = function
        .clone()
        .with_resource_summary(vec![input.clone()], vec![output.clone(), output]);
    let transfer = prepare_scalar_transfer(&duplicate, pointer.clone(), caller.clone(), &facts);
    assert!(transfer.consumed_cell_returns.get(0).is_some());
    assert!(transfer.consumed_cell_returns.get(1).is_none());
    let borrowed = function.with_resource_summary(
        vec![input.clone().with_role(ResourceTransferRole::Borrow)],
        vec![
            input
                .with_role(ResourceTransferRole::Borrow)
                .with_state_source(ResourceStateSource::Entry),
        ],
    );
    let transfer = prepare_scalar_transfer(&borrowed, pointer, caller, &facts);
    assert!(transfer.consumed_cell_returns.get(0).is_none());
}

pub(super) fn mixed_scalar_contract(duplicate: bool, overlap: bool) -> ProgramFunction {
    use crate::kernel::program_expression::{int32_literal, variable};
    let scalar = |name| {
        ResourceSpec::owned_memory(MemorySegment::new(
            variable(name),
            int32_literal(0),
            int32_literal(1),
        ))
    };
    let borrowed = scalar("q")
        .with_role(ResourceTransferRole::Borrow)
        .with_state_source(ResourceStateSource::Entry);
    let produced = |name| {
        scalar(name)
            .with_role(ResourceTransferRole::Produce)
            .with_state_source(ResourceStateSource::Post)
    };
    let ticket = ResourceSpec::declared(
        ResourceFamily::Token,
        ResourceAccessMode::Own,
        "mixed_ticket".into(),
        vec![],
        vec![],
        ResourceTransferRole::Produce,
        ResourceStateSource::Post,
    )
    .unwrap();
    let skipped = ticket.clone().with_guard(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(int32_literal(0)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(int32_literal(1)),
    });
    let mut outputs = vec![
        skipped,
        borrowed.clone(),
        produced("r"),
        ticket,
        produced("p"),
    ];
    if duplicate {
        outputs.push(produced("p"));
    }
    if overlap {
        outputs.push(
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("q"),
                int32_literal(1),
                int32_literal(2),
            ))
            .with_role(ResourceTransferRole::Produce)
            .with_state_source(ResourceStateSource::Post),
        );
    }
    program_function(
        ProgramType::Void,
        "mixed_scalar_transfers",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
            program_parameter("r", ProgramType::Int32Pointer),
        ],
        program_skip(),
    )
    .with_resource_summary(
        vec![
            scalar("p").with_role(ResourceTransferRole::Consume),
            borrowed,
            scalar("r").with_role(ResourceTransferRole::Consume),
        ],
        outputs,
    )
}

pub(super) fn mixed_scalar_state() -> ExecutionState {
    let mut state = ExecutionState::new().with_population_creation_tracking();
    let mut resources = ResourceContext::new();
    for (index, name) in ["p", "q", "r"].into_iter().enumerate() {
        let pointer = Address::symbolic(Variable(8_880_000 + index as u64));
        let memory = state.memory().clone().with_block(pointer.base.clone(), 8);
        state = state
            .with_local(name, ProgramValue::pointer(pointer.clone()))
            .with_memory(memory);
        resources = resources.unchecked_with_fact(owner(pointer, 0, 1));
    }
    state.with_resource_context(resources)
}

pub(super) fn prepare_mixed_scalar(
    function: &ProgramFunction,
    state: &ExecutionState,
    facts: &PureFactContext,
) -> FunctionResourceTransfer {
    prepare_contract_resource_transfer(
        state,
        state,
        function.name(),
        function.contract_interface(),
        facts,
        &mut ExecutionBudget::beside_live_state(),
        false,
        ResourceTransitionPurpose::CallSite,
    )
    .unwrap()
    .unwrap()
}

pub(super) fn evaluate_mixed_scalar(
    function: &ProgramFunction,
    state: &ExecutionState,
    transfer: &FunctionResourceTransfer,
    facts: &PureFactContext,
) -> Result<EvaluatedReturnResources, RuntimeError> {
    evaluate_contract_return_resource_context(
        function.contract_interface(),
        &transfer.canonical_borrowed_owners,
        &transfer.borrowed_inputs,
        &transfer_entry_clauses(transfer),
        state,
        state,
        function.contract_interface().resource_ensures().len(),
        &[],
        ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
        facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
}

#[test]
fn mixed_return_occurrences_carry_distinct_transfers_past_a_skipped_clause() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let state = mixed_scalar_state();
    let function = mixed_scalar_contract(false, false);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let p = transfer.consumed_cell_returns.get(4).unwrap();
    let r = transfer.consumed_cell_returns.get(2).unwrap();
    assert_ne!(p.input, r.input);
    assert_eq!(
        evaluated
            .occurrences
            .iter()
            .map(|entry| entry.origin)
            .collect::<Vec<_>>(),
        vec![
            ReturnOwnershipOrigin::EntryBorrow,
            ReturnOwnershipOrigin::ConsumedCell(r),
            ReturnOwnershipOrigin::Description,
            ReturnOwnershipOrigin::ConsumedCell(p),
        ]
    );
    for _ in 0..2 {
        let prepared = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap();
        assert_eq!(prepared.pending.facts().len(), 1);
        let (destination, mappings) = prepared.finish(&facts).unwrap();
        assert_eq!(
            mappings
                .iter()
                .map(|mapping| mapping.consumed_input)
                .collect::<Vec<_>>(),
            vec![None, Some(r.input), None, Some(p.input)]
        );
        for (mapping, entry) in mappings.iter().zip(&evaluated.occurrences) {
            assert_eq!(mapping.source, entry.source);
            assert_eq!(
                destination.owned_fact_for_occurrence(mapping.destination),
                evaluated.resources.owned_fact_for_occurrence(entry.source)
            );
        }
    }
    assert_eq!(state.resources().facts().len(), 3);
}

#[test]
fn a_consumed_cell_cannot_supply_two_return_occurrences() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let state = mixed_scalar_state();
    let function = mixed_scalar_contract(true, false);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    assert!(transfer.consumed_cell_returns.get(4).is_some());
    assert!(transfer.consumed_cell_returns.get(5).is_none());
    assert!(evaluate_mixed_scalar(&function, &state, &transfer, &facts).is_err());
}

#[test]
fn ordinary_outputs_still_validate_against_a_mixed_return_frame() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let state = mixed_scalar_state();
    let retained = owner(Address::symbolic(Variable(8_880_001)), 1, 2);
    let state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(retained));
    let function = mixed_scalar_contract(false, true);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    assert_eq!(
        evaluated.occurrences.last().unwrap().origin,
        ReturnOwnershipOrigin::Description
    );
    assert!(
        evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements,
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .is_err()
    );
}

#[test]
fn raw_composition_does_not_exercise_a_consumed_occurrences_transfer() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let state = mixed_scalar_state();
    let function = mixed_scalar_contract(false, false);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let prepared = evaluated
        .restore_entry_borrows(
            state.resources().clone(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(prepared.restored.is_empty());
    assert_eq!(prepared.pending.facts().len(), 4);
    assert!(prepared.finish(&facts).is_err());
}

#[test]
fn single_source_origin_stays_aligned_after_a_joined_borrow() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let state = mixed_scalar_state();
    let q = Address::symbolic(Variable(8_880_001));
    let state = state.clone().with_resource_context(
        state
            .resources()
            .clone()
            .unchecked_with_fact(owner(q, 1, 2)),
    );
    let segment =
        |name, end| MemorySegment::new(variable(name), int32_literal(0), int32_literal(end));
    let borrowed = ResourceSpec::owned_memory(segment("q", 2))
        .with_role(ResourceTransferRole::Borrow)
        .with_state_source(ResourceStateSource::Entry);
    let input =
        ResourceSpec::owned_memory(segment("p", 1)).with_role(ResourceTransferRole::Consume);
    let output = ResourceSpec::owned_memory(segment("p", 1))
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
    let function = program_function(
        ProgramType::Void,
        "joined_borrow",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        program_skip(),
    )
    .with_resource_summary(vec![borrowed.clone(), input], vec![borrowed, output]);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    let plan = transfer.stable_view_plan.as_ref().unwrap();
    assert_eq!(plan.transferred_ownership_sources.len(), 2);
    assert_eq!(plan.transferred_ownership_sources[0], None);
    assert_eq!(
        plan.transferred_ownership_sources[1],
        Some(transfer.consumed_cell_returns.get(1).unwrap().input)
    );
}

#[test]
fn a_borrowed_composites_post_footprint_cannot_overlap_a_transferred_cell() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let cell = Address::symbolic(Variable(8_895_000));
    let field = Address::symbolic(Variable(8_895_001));
    let old_child = Address::symbolic(Variable(8_895_002));
    let scalar = scalar_transfer_contract(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ));
    let owner = owner(cell.clone(), 0, 1);
    let selected = prepare_scalar_transfer(
        &scalar,
        cell.clone(),
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner.clone()),
        &facts,
    )
    .consumed_cell_returns
    .get(0)
    .unwrap();
    let field_value = ProgramValue::typed_pointer(field.clone(), ProgramType::Int32PointerPointer);
    let borrowed_spec = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        "moving_return".into(),
        vec![ProgramExpression::Value(field_value.clone())],
        vec![ProgramType::Int32PointerPointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let borrowed = ResourceFact::own_composite("moving_return".into(), vec![field_value]);
    let checked_borrow = CheckedResourceFact {
        fact: borrowed.clone(),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: Some(1),
        selected_mutex_source: None,
    };
    let mut checked = vec![CheckedResourceFact {
        fact: owner.clone(),
        role: ResourceTransferRole::Consume,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: Some(0),
        selected_mutex_source: None,
    }];
    checked.push(checked_borrow.clone());
    let child = ProgramExpression::TypedLoad {
        pointer: Box::new(variable("link")),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let function = program_function(
        ProgramType::Void,
        "moving_return",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_skip(),
    )
    .with_resource_summary(
        vec![
            scalar.contract_interface().resource_requires()[0].clone(),
            borrowed_spec.clone(),
        ],
        vec![
            borrowed_spec,
            scalar.contract_interface().resource_ensures()[0].clone(),
        ],
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "moving_return",
        vec![program_parameter("link", ProgramType::Int32PointerPointer)],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(
                MemorySegment::new(variable("link"), int32_literal(0), int32_literal(1))
                    .with_element_width(C_POINTER_BYTE_WIDTH),
            ),
            ResourceSpec::owned_memory(MemorySegment::new(
                child,
                int32_literal(0),
                int32_literal(1),
            )),
        ],
        vec![],
    )]);
    let memory = SymbolicMemory::new()
        .with_block(field.base.clone(), C_POINTER_BYTE_WIDTH)
        .with_block(old_child.base.clone(), 4)
        .with_block(cell.base.clone(), 4)
        .store(field.clone(), ProgramValue::pointer(old_child));
    let entry = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(cell.clone()))
        .with_memory(memory.clone())
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_facts([owner, borrowed]),
        );
    let post = entry
        .clone()
        .with_memory(memory.store(field, ProgramValue::pointer(cell)))
        .with_resource_context(ResourceContext::new_with_equalities(&facts));
    let transfers = ConsumedCellReturns {
        frontier: None,
        direct: BTreeMap::from([(1, selected)]),
        children: BTreeMap::new(),
        borrowed: BTreeMap::new(),
        constructed: BTreeMap::new(),
    };
    let result = evaluate_contract_return_resources(
        &ResourceContext::new_with_equalities(&facts),
        &[],
        &[],
        &[checked_borrow],
        &checked,
        &entry,
        &post,
        function.name(),
        function.contract_interface(),
        &[],
        ReturnResourceComposition::ApplyTransfers(&transfers),
        &facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert!(matches!(
        result,
        Err(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
    ));
}

pub(super) fn fixed_range_contract(
    pointer_type: ProgramType,
    input: MemorySegment,
    output: MemorySegment,
) -> ProgramFunction {
    program_function(
        ProgramType::Void,
        "fixed_range_transfer",
        vec![program_parameter("p", pointer_type)],
        program_skip(),
    )
    .with_resource_summary(
        vec![
            ResourceSpec::owned_memory(input.with_uninitialized(true))
                .with_role(ResourceTransferRole::Consume),
        ],
        vec![
            ResourceSpec::owned_memory(output)
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post),
        ],
    )
}

#[test]
fn fixed_range_transfers_preserve_typed_widths_and_partial_frames() {
    use crate::kernel::program_expression::{int32_literal, int64_literal, variable};
    for (pointer_type, width, start, end) in [
        (ProgramType::UInt8Pointer, 1, 2, 7),
        (ProgramType::Int16Pointer, 2, 1, 4),
        (ProgramType::Int64Pointer, 8, 2, 5),
        (ProgramType::Int32Pointer, 16, 1, 3),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let pointer = Address::symbolic(Variable(8_910_000));
        let owner = |from, to| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer.clone(),
                MachineTerm::constant(from),
                MachineTerm::constant(to),
                width,
            ))
        };
        let original = owner(0, end + 2);
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 1024))
            .with_local(
                "p",
                ProgramValue::typed_pointer(pointer.clone(), pointer_type),
            )
            .with_resource_context(
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(original.clone()),
            );
        let bound = |value: u32| {
            if width == 8 {
                int64_literal(i64::from(value))
            } else {
                int32_literal(value)
            }
        };
        let segment =
            MemorySegment::new(variable("p"), bound(start), bound(end)).with_element_width(width);
        let function = fixed_range_contract(pointer_type, segment.clone(), segment);
        let transfer = prepare_mixed_scalar(&function, &state, &facts);
        let selected = transfer
            .consumed_cell_returns
            .get(0)
            .expect("fixed range transfer");
        assert_eq!(
            state.resources().owned_fact_for_occurrence(selected.input),
            Some(&original)
        );
        let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
        assert_eq!(
            evaluated.occurrences[0].origin,
            ReturnOwnershipOrigin::ConsumedCell(selected)
        );
        for _ in 0..2 {
            let (result, mapping) = evaluated
                .restore_entry_borrows(
                    transfer.caller_resources_after_requirements.clone(),
                    ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                    &facts,
                )
                .unwrap()
                .finish(&facts)
                .unwrap();
            assert_eq!(mapping[0].consumed_input, Some(selected.input));
            assert!(result.satisfies_fact(&owner(0, end + 2), &facts));
            let retained = result
                .without_exact_representation_for_occurrence(mapping[0].destination)
                .unwrap();
            assert!(retained.satisfies_fact(&owner(0, start), &facts));
            assert!(retained.satisfies_fact(&owner(end, end + 2), &facts));
            assert!(!retained.satisfies_fact(&owner(start, end), &facts));
        }
        assert_eq!(state.resources().facts(), &[original]);
    }
}

#[test]
fn fixed_range_matching_retains_bound_types_width_and_single_use() {
    use crate::kernel::program_expression::{int32_literal, uint64_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_910_001));
    let segment =
        MemorySegment::new(variable("p"), int32_literal(2), int32_literal(5)).with_element_width(8);
    let function =
        fixed_range_contract(ProgramType::Int64Pointer, segment.clone(), segment.clone());
    let state = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int64Pointer),
        )
        .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 1024))
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_facts([
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer.clone(),
                    2u32.into(),
                    5u32.into(),
                    8,
                )),
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer,
                    6u32.into(),
                    8u32.into(),
                    8,
                )),
            ]),
        );
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    let input = function.contract_interface().resource_requires()[0].clone();
    let output = |segment| {
        ResourceSpec::owned_memory(segment)
            .with_role(ResourceTransferRole::Produce)
            .with_state_source(ResourceStateSource::Post)
    };
    for changed in [
        MemorySegment::new(variable("p"), int32_literal(3), int32_literal(6)).with_element_width(8),
        MemorySegment::new(variable("p"), int32_literal(2), int32_literal(6)).with_element_width(8),
        MemorySegment::new(variable("p"), int32_literal(2), int32_literal(5)).with_element_width(4),
        MemorySegment::new(variable("p"), uint64_literal(2), uint64_literal(5))
            .with_element_width(8),
        MemorySegment::new(variable("p"), variable("index"), int32_literal(5))
            .with_element_width(8),
    ] {
        let changed = function
            .clone()
            .with_resource_summary(vec![input.clone()], vec![output(changed)]);
        assert!(
            ConsumedCellReturns::prepare(
                changed.contract_interface(),
                transfer.stable_view_plan.as_ref().unwrap(),
                state.resources()
            )
            .get(0)
            .is_none()
        );
    }
    let other =
        MemorySegment::new(variable("p"), int32_literal(6), int32_literal(8)).with_element_width(8);
    let reversed = function.clone().with_resource_summary(
        vec![
            input.clone(),
            ResourceSpec::owned_memory(other.clone().with_uninitialized(true))
                .with_role(ResourceTransferRole::Consume),
        ],
        vec![output(other), output(segment.clone())],
    );
    let reversed_transfer = prepare_mixed_scalar(&reversed, &state, &facts);
    for (index, start) in [(0, 6), (1, 2)] {
        let selected = reversed_transfer.consumed_cell_returns.get(index).unwrap();
        assert_eq!(
            state
                .resources()
                .owned_fact_for_occurrence(selected.input)
                .unwrap()
                .memory_own_range()
                .unwrap()
                .constant_start(),
            Some(start)
        );
    }
    let duplicate =
        function.with_resource_summary(vec![input], vec![output(segment.clone()), output(segment)]);
    let selected = ConsumedCellReturns::prepare(
        duplicate.contract_interface(),
        transfer.stable_view_plan.as_ref().unwrap(),
        state.resources(),
    );
    assert!(selected.get(0).is_some());
    assert!(selected.get(1).is_none());
}

#[test]
fn fixed_wide_range_returns_keep_their_original_index_kind() {
    use crate::kernel::program_expression::{uint64_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_910_002));
    let range = |start, end| {
        ResourceFact::own_memory(MemoryRange::new_wide(
            pointer.clone(),
            MachineTerm::uint64_constant(start),
            MachineTerm::uint64_constant(end),
            8,
        ))
    };
    let state = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int64Pointer),
        )
        .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 1024))
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(range(0, 8)),
        );
    let segment = MemorySegment::new(variable("p"), uint64_literal(2), uint64_literal(5))
        .with_element_width(8);
    let function = fixed_range_contract(ProgramType::Int64Pointer, segment.clone(), segment);
    let transfer = prepare_mixed_scalar(&function, &state, &facts);
    assert!(transfer.consumed_cell_returns.get(0).is_some());
    let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
    let (result, mapping) = evaluated
        .restore_entry_borrows(
            transfer.caller_resources_after_requirements,
            ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    assert!(
        result
            .owned_fact_for_occurrence(mapping[0].destination)
            .unwrap()
            .memory_own_range()
            .unwrap()
            .wide_bounds()
            .is_some()
    );
    assert!(result.satisfies_fact(&range(0, 8), &facts));
}

pub(super) fn flat_body_definition(
    name: &str,
    pointer: &Address,
    count: u32,
) -> CompositeResourceDefinition {
    use crate::kernel::program_expression::int32_literal;
    let base = ProgramExpression::Value(ProgramValue::pointer(pointer.clone()));
    let mut children = (0..count)
        .map(|index| {
            ResourceSpec::owned_memory(MemorySegment::new(
                base.clone(),
                int32_literal(index * 2),
                int32_literal(index * 2 + 1),
            ))
        })
        .collect::<Vec<_>>();
    children.push(ResourceSpec::viewed_memory(MemorySegment::new(
        base,
        int32_literal(count * 2 + 2),
        int32_literal(count * 2 + 3),
    )));
    CompositeResourceDefinition::new(name, vec![], None, false, children, vec![])
}

#[test]
fn flat_composite_return_carries_its_body_through_frontier_and_projection() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_001));
    let definition = flat_body_definition("flat_return", &pointer, 2);
    let state = ExecutionState::new();
    let head = ResourceFact::own_composite("flat_return".into(), vec![]);
    // Equal heads must retain separate constructions and support lifetimes.
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap()
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let bodies = ConstructedReturnBodies::construct(&evaluated, &[definition], &state, &facts);
    assert_eq!(bodies.0.len(), 2);
    for entry in &evaluated.occurrences {
        let body = bodies.get(entry.source).unwrap();
        assert_eq!(body.frontier.len(), 3);
        assert_eq!(body.expansion, body.frontier);
    }
    let prepared = evaluated
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
            &facts,
        )
        .unwrap();
    let held = ResourceContext::new().unchecked_with_fact(owner(pointer, 0, 1));
    // Definitions are deliberately absent: both consumers must use the
    // selected occurrence's construction, including on an overlap refusal.
    for borrowed in [true, false] {
        assert!(matches!(
            produced_composite_frontier_conflict(
                &held,
                prepared
                    .frontier_sources(&evaluated.resources, borrowed)
                    .map(|(source, fact)| (fact, bodies.get(source))),
                &facts
            ),
            Some(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
        ));
    }
    let (mut destination, transfers) = prepared.finish(&facts).unwrap();
    let projected = project_return_resource_cores(
        &evaluated.resources,
        &transfers,
        &bodies,
        &facts,
        &destination,
    );
    let mut views = Vec::new();
    for projection in projected {
        assert_eq!(projection.frontier.len(), 3);
        let (next, inserted) = destination
            .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                projection.destination,
                &projection.support,
                projection.projected,
                state.memory(),
            );
        destination = next.with_cached_supported_expansion_for_occurrence(
            projection.destination,
            &projection.support,
            projection.expansion,
        );
        views.push(inserted.into_iter().map(|(_, id)| id).collect::<Vec<_>>());
    }
    for removed in 0..2 {
        let branch = destination
            .clone()
            .without_exact_representation_for_occurrence(transfers[removed].destination)
            .unwrap();
        assert!(
            views[removed]
                .iter()
                .all(|id| branch.view_fact_for_occurrence(*id).is_none())
        );
        assert!(
            views[1 - removed]
                .iter()
                .all(|id| branch.view_fact_for_occurrence(*id).is_some())
        );
        assert!(
            destination
                .owned_fact_for_occurrence(transfers[removed].destination)
                .is_some()
        );
    }
}

#[test]
fn unsupported_return_families_refuse_in_dispatch() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_002));
    let mut nested = flat_body_definition("nested", &pointer, 1);
    nested.contains.push(
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "missing-child".into(),
            vec![],
            vec![],
            ResourceTransferRole::Produce,
            ResourceStateSource::Current,
        )
        .unwrap(),
    );
    for (name, definitions) in [("nested", vec![nested]), ("missing", vec![])] {
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                ResourceFact::own_composite(name.into(), vec![]),
                ReturnOwnershipOrigin::Description,
                &facts,
            )
            .unwrap();
        let _fast = crate::kernel::search::FastOperationScope::enter("unsupported return family");
        assert!(
            ConstructedReturnBodies::try_construct(
                &evaluated,
                &definitions,
                &ExecutionState::new(),
                ReturnResourceComposition::ValidateDescriptions,
                &facts,
            )
            .is_none()
        );
        assert_eq!(evaluated.resources.facts().len(), 1);
    }
}

#[test]
fn nonunit_memory_returns_refuse_but_token_counts_keep_their_constructed_body() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_003));
    for memory in [false, true] {
        let definition = if memory {
            flat_body_definition("many", &pointer, 1)
        } else {
            CompositeResourceDefinition::new("many", vec![], None, false, vec![], vec![])
        };
        let head = ResourceFact::Own(
            Resource::Composite {
                name: "many".into(),
                arguments: vec![].into(),
            },
            Box::new(MachineTerm::constant(2)),
        );
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        let _fast = crate::kernel::search::FastOperationScope::enter("nonunit return family");
        let bodies = ConstructedReturnBodies::construct(
            &evaluated,
            &[definition],
            &ExecutionState::new(),
            &facts,
        );
        let body = bodies.for_return(evaluated.occurrences[0].source, &head);
        let error = produced_composite_frontier_conflict(
            &ResourceContext::new_with_equalities(&facts),
            std::iter::once((&head, body)),
            &facts,
        );
        assert_eq!(error.is_some(), memory);
    }
}

#[test]
fn sealed_return_dispatch_retains_opaque_identity_and_projection_needs_no_definition() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_004));
    let (head, mut definition) = super::specialized_return_tests::named(pointer, 8_819_008);
    definition.sealed = true;
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let source = evaluated.occurrences[0].source;
    let _fast = crate::kernel::search::FastOperationScope::enter("opaque return family");
    let state = ExecutionState::new();
    let bodies = ConstructedReturnBodies::construct(&evaluated, &[definition], &state, &facts);
    let body = bodies.get(source).unwrap();
    assert_eq!(body.folded, vec![(head.clone(), source)]);
    assert!(body.frontier.is_empty());
    let (destination, transfers) = evaluated
        .restore_entry_borrows(
            ResourceContext::new_with_equalities(&facts),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    let projected = project_return_resource_cores(
        &evaluated.resources,
        &transfers,
        &bodies,
        &facts,
        &destination,
    );
    assert_eq!(projected[0].expansion, vec![head]);
    assert!(projected[0].frontier.is_empty());
    assert!(projected[0].viewed_children.as_slice().is_empty());
}

#[test]
fn sealed_field_free_returns_keep_their_explicit_memory_frontier() {
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_819_009));
    let mut definition = flat_body_definition("sealed_memory", &p, 1);
    definition.sealed = true;
    let head = ResourceFact::own_composite("sealed_memory".into(), vec![]);
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let _fast = crate::kernel::search::FastOperationScope::enter("sealed finite frontier");
    let bodies =
        ConstructedReturnBodies::construct(&outputs, &[definition], &ExecutionState::new(), &facts);
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    assert!(body.folded.is_empty());
    assert!(
        body.frontier
            .iter()
            .any(|piece| piece.memory_own_range().is_some())
    );
    let held = ResourceFact::own_memory(MemoryRange::new(p, 0u32.into(), 1u32.into()));
    assert!(matches!(
        produced_composite_frontier_conflict(
            &ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held),
            std::iter::once((&head, Some(body))),
            &facts,
        ),
        Some(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
    ));
}

#[test]
fn logical_opaque_instances_do_not_invent_hidden_escrow_ownership() {
    let facts = PureFactContext::new();
    let (head, mut definition) =
        super::specialized_return_tests::named(Address::symbolic(Variable(8_819_010)), 8_819_011);
    definition.sealed = true;
    definition.contains.clear();
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let _fast = crate::kernel::search::FastOperationScope::enter("logical opaque instance");
    let bodies =
        ConstructedReturnBodies::construct(&outputs, &[definition], &ExecutionState::new(), &facts);
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    assert_eq!(body.expansion, vec![head.clone()]);
    assert!(body.escrow_boundary().is_empty());
    let mut boundary = EscrowRecoveryBoundary::default();
    boundary.record(
        outputs.occurrences[0].source,
        vec![],
        body.escrow_boundary(),
    );
    // The opaque instance still exists, with its fields, but its empty body
    // cannot conflict with the independently checked memory/loan partition.
    boundary
        .admit(
            &ResourceContext::new_with_equalities(&facts),
            true,
            &outputs.resources,
            &facts,
        )
        .unwrap();
}

#[test]
fn opaque_instances_keep_the_actual_fields_without_opening_unhandled_children() {
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_819_005));
    let (head, mut definition) = super::specialized_return_tests::named(p.clone(), 8_819_006);
    definition.contains.push(composite_spec(
        "unopened_child",
        ProgramExpression::Value(ProgramValue::pointer(p)),
        ResourceTransferRole::Borrow,
    ));
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let source = evaluated.occurrences[0].source;
    let _fast = crate::kernel::search::FastOperationScope::enter("opaque selected instance");
    // There is deliberately no child definition or authority to reconstruct.
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[definition.clone()],
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(source).unwrap();
    assert_eq!(body.folded, vec![(head.clone(), source)]);
    assert_eq!(body.expansion, vec![head]);
    assert!(body.frontier.is_empty());
    assert!(body.transfers.is_empty());
}

#[test]
fn nonunit_memory_cannot_hide_behind_borrowed_child_custody() {
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_819_007));
    let head = ResourceFact::Own(
        Resource::Composite {
            name: "many".into(),
            arguments: vec![].into(),
        },
        Box::new(2u32.into()),
    );
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap();
    let plan = ConsumedCellReturns::default();
    let _fast = crate::kernel::search::FastOperationScope::enter("counted borrowed return");
    let bodies = ConstructedReturnBodies::try_construct(
        &outputs,
        &[flat_body_definition("many", &p, 1)],
        &ExecutionState::new(),
        ReturnResourceComposition::ApplyTransfers(&plan),
        &facts,
    )
    .unwrap();
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    // An entry-borrow role without a selected input provides no byte custody.
    assert!(
        body.boundary
            .iter()
            .any(|piece| piece.memory_own_range().is_some())
    );
    assert!(
        produced_composite_frontier_conflict(
            &ResourceContext::new_with_equalities(&facts),
            std::iter::once((&head, Some(body))),
            &facts
        )
        .is_some()
    );
}

pub(super) fn constructed_flat_return(
    pointer: &Address,
    count: u32,
    facts: &PureFactContext,
) -> (EvaluatedReturnResources, ConstructedReturnBodies) {
    let evaluated = EvaluatedReturnResources::new(facts)
        .admit(
            ResourceFact::own_composite("boundary_return".into(), vec![]),
            ReturnOwnershipOrigin::Description,
            facts,
        )
        .unwrap();
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[flat_body_definition("boundary_return", pointer, count)],
        &ExecutionState::new(),
        facts,
    );
    assert_eq!(bodies.0.len(), 1);
    (evaluated, bodies)
}

#[test]
fn flat_body_admission_keeps_selected_alias_diagnostics_and_branch_isolation() {
    let pointer = Address::symbolic(Variable(8_819_100));
    let alias = Address::symbolic(Variable(8_819_101));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::address_equal(pointer.clone(), alias.clone()),
        true,
    );
    let (evaluated, bodies) = constructed_flat_return(&pointer, 2, &facts);
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    // The packaged view may overlap a retained owner; only owned leaves
    // introduce a new exclusive footprint.
    let parent = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts([owner(alias.clone(), 4, 5), owner(alias.clone(), 6, 7)]);
    parent.synchronize_memory_equalities(&facts);
    assert!(matches!(
        parent.admit_returned_frontier(body.boundary(), &facts),
        FlatBodyAdmission::Admitted
    ));
    let overlapping = owner(alias, 2, 3);
    let branch = parent.clone().unchecked_with_fact(overlapping.clone());
    branch.synchronize_memory_equalities(&facts);
    let FlatBodyAdmission::Conflict { piece, held } =
        branch.admit_returned_frontier(body.boundary(), &facts)
    else {
        panic!("an aliased body leaf must conflict");
    };
    assert_eq!(*piece, owner(pointer, 2, 3));
    assert_eq!(*held, overlapping);
    assert_eq!(branch.facts().len(), 3);
    assert_eq!(parent.facts().len(), 2);
    assert!(matches!(
        parent.admit_returned_frontier(body.boundary(), &facts),
        FlatBodyAdmission::Admitted
    ));
}

#[test]
fn flat_body_admission_uses_cold_coordinates_but_refuses_general_geometry() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_102));
    let (evaluated, bodies) = constructed_flat_return(&pointer, 1, &facts);
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    let cold = ResourceContext::new().unchecked_with_fact(owner(pointer.clone(), 0, 1));
    assert!(matches!(
        cold.admit_returned_frontier(body.boundary(), &facts),
        FlatBodyAdmission::Conflict { .. }
    ));
    // A cold lookup now reports the conflict without discovery.
    assert!(matches!(
        produced_composite_frontier_conflict(
            &cold,
            std::iter::once((
                evaluated
                    .resources
                    .owned_fact_for_occurrence(evaluated.occurrences[0].source)
                    .unwrap(),
                Some(body)
            )),
            &facts
        ),
        Some(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
    ));
    let symbolic = ResourceFact::own_memory(MemoryRange::new(
        pointer,
        0u32.into(),
        MachineTerm::Variable(Variable(8_819_103)),
    ));
    let general = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(symbolic);
    general.synchronize_memory_equalities(&facts);
    assert!(matches!(
        general.admit_returned_frontier(body.boundary(), &facts),
        FlatBodyAdmission::Unestablished(_)
    ));
}

pub(super) fn composite_spec(
    name: &str,
    base: ProgramExpression,
    role: ResourceTransferRole,
) -> ResourceSpec {
    ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        name.into(),
        vec![base],
        vec![ProgramType::Int32Pointer],
        role,
        ResourceStateSource::Post,
    )
    .unwrap()
}

pub(super) fn nested_transfer_function(depth: usize) -> ProgramFunction {
    use crate::kernel::program_expression::{int32_literal, variable};
    let mut definitions = vec![CompositeResourceDefinition::new(
        "layer_0000",
        vec![program_parameter("cell", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("cell"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    )];
    for index in 1..depth {
        definitions.push(CompositeResourceDefinition::new(
            format!("layer_{index:04}"),
            vec![program_parameter("cell", ProgramType::Int32Pointer)],
            None,
            false,
            vec![composite_spec(
                &format!("layer_{:04}", index - 1),
                variable("cell"),
                ResourceTransferRole::Borrow,
            )],
            vec![],
        ));
    }
    let input = ResourceSpec::owned_memory(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ))
    .with_role(ResourceTransferRole::Consume);
    program_function(
        ProgramType::Void,
        "nested_transfer",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_skip(),
    )
    .with_resource_summary(
        vec![input],
        vec![composite_spec(
            &format!("layer_{:04}", depth - 1),
            variable("p"),
            ResourceTransferRole::Produce,
        )],
    )
    .with_composite_resource_definitions(definitions)
}

#[test]
fn composite_children_carry_consumed_sources_selected_before_return_lowering() {
    for depth in [1, 4] {
        let facts = PureFactContext::new();
        let pointer = Address::symbolic(Variable(8_819_200));
        let function = nested_transfer_function(depth);
        let caller = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
            pointer.clone(),
            0,
            1,
        ));
        let transfer = prepare_scalar_transfer(&function, pointer.clone(), caller, &facts);
        let path = std::iter::repeat_n(0, depth + 1).collect::<Vec<_>>();
        assert_eq!(transfer.consumed_cell_returns.children.len(), 1);
        let selected = transfer.consumed_cell_returns.children[&path];
        let state = ExecutionState::new().with_local("p", ProgramValue::pointer(pointer));
        let evaluated = evaluate_mixed_scalar(&function, &state, &transfer, &facts).unwrap();
        let bodies = ConstructedReturnBodies::try_construct(
            &evaluated,
            function
                .contract_interface()
                .composite_resource_definitions(),
            &state,
            ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
            &facts,
        )
        .unwrap();
        let body = bodies.get(evaluated.occurrences[0].source).unwrap();
        let leaf = body.transfers.last().unwrap();
        assert_eq!(leaf.origin, ReturnOwnershipOrigin::ConsumedCell(selected));
        assert!(body.boundary.is_empty());
        assert_eq!(body.transfers.len(), depth);
        assert_eq!(body.transfers[0].parent, evaluated.occurrences[0].source);
        for pair in body.transfers.windows(2) {
            assert_eq!(pair[1].parent, pair[0].source);
        }
        assert!(matches!(
            ResourceContext::new().admit_returned_frontier(body.boundary(), &facts),
            FlatBodyAdmission::Admitted
        ));
        // The raw-description route cannot exercise the selected transfer.
        let raw = ConstructedReturnBodies::try_construct(
            &evaluated,
            function
                .contract_interface()
                .composite_resource_definitions(),
            &state,
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
        assert_eq!(
            raw.get(evaluated.occurrences[0].source)
                .unwrap()
                .boundary
                .len(),
            1
        );
    }
}

#[test]
fn invariant_borrowed_children_retain_origin_without_granting_it_to_descriptions() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_201));
    let function = nested_transfer_function(3);
    let head =
        ResourceFact::own_composite("layer_0002".into(), vec![ProgramValue::pointer(pointer)]);
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head, ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap();
    let state = ExecutionState::new();
    let bodies = ConstructedReturnBodies::try_construct(
        &evaluated,
        function
            .contract_interface()
            .composite_resource_definitions(),
        &state,
        ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
        &facts,
    )
    .unwrap();
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert_eq!(
        body.transfers.last().unwrap().origin,
        ReturnOwnershipOrigin::EntryBorrow
    );
    assert!(body.boundary.is_empty());
}

#[test]
fn decided_conditional_bodies_and_opaque_guards_are_constructed_once() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_202));
    let mut definition = flat_body_definition("conditional_return", &pointer, 1);
    definition.parameters = vec![program_parameter("flag", ProgramType::Int32)];
    definition.condition = Some(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(variable("flag")),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(int32_literal(0)),
    });
    for (flag, count) in [
        (ProgramValue::Int32(MachineTerm::constant(0)), 2),
        (ProgramValue::Int32(MachineTerm::constant(1)), 0),
        (
            ProgramValue::Int32(MachineTerm::Variable(Variable(8_819_203))),
            1,
        ),
    ] {
        let head = ResourceFact::own_composite("conditional_return".into(), vec![flag]);
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
        let bodies = ConstructedReturnBodies::construct(
            &evaluated,
            &[definition.clone()],
            &ExecutionState::new(),
            &facts,
        );
        let body = bodies.get(evaluated.occurrences[0].source).unwrap();
        assert_eq!(body.expansion.len(), count);
        let (destination, transfers) = evaluated
            .restore_entry_borrows(
                ResourceContext::new(),
                ReturnResourceComposition::ValidateDescriptions,
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        let projected = project_return_resource_cores(
            &evaluated.resources,
            &transfers,
            &bodies,
            &facts,
            &destination,
        );
        assert_eq!(projected[0].expansion, body.expansion);
    }
}

#[test]
fn nested_body_normalization_keeps_distinct_child_identities_and_checks_internal_overlap() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_204));
    let function = nested_transfer_function(3);
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own_composite(
                "layer_0002".into(),
                vec![ProgramValue::pointer(pointer.clone())],
            ),
            ReturnOwnershipOrigin::Description,
            &facts,
        )
        .unwrap();
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        function
            .contract_interface()
            .composite_resource_definitions(),
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert_eq!(
        body.transfers
            .iter()
            .map(|transfer| transfer.source)
            .collect::<BTreeSet<_>>()
            .len(),
        3
    );
    assert_eq!(body.expansion, vec![owner(pointer.clone(), 0, 1)]);
    let frame =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(pointer, 0, 1));
    frame.synchronize_memory_equalities(&facts);
    assert!(matches!(
        frame.admit_returned_frontier(body.boundary(), &facts),
        FlatBodyAdmission::Conflict { .. }
    ));
    let mut definitions = function
        .contract_interface()
        .composite_resource_definitions()
        .to_vec();
    let duplicate = definitions[2].contains[0].clone();
    definitions[2].contains.push(duplicate);
    assert!(
        ConstructedReturnBodies::try_construct(
            &evaluated,
            &definitions,
            &ExecutionState::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        )
        .is_none()
    );
}

#[test]
#[should_panic(expected = "returned composite must carry its constructed or opaque body")]
fn composite_consumers_refuse_missing_construction_metadata() {
    let facts = PureFactContext::new();
    let head = ResourceFact::own_composite("omitted_body".into(), vec![]);
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    ConstructedReturnBodies::default().for_return(evaluated.occurrences[0].source, &head);
}

pub(super) fn viewed_child_definitions(
    data: Address,
    depth: usize,
) -> Vec<CompositeResourceDefinition> {
    use crate::kernel::program_expression::{int32_literal, variable};
    let mut definitions = vec![CompositeResourceDefinition::new(
        "view_level_0000",
        vec![program_parameter("v", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("v"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    )];
    for index in 1..depth {
        definitions.push(CompositeResourceDefinition::new(
            format!("view_level_{index:04}"),
            vec![program_parameter("v", ProgramType::Int32Pointer)],
            None,
            false,
            vec![composite_spec(
                &format!("view_level_{:04}", index - 1),
                variable("v"),
                ResourceTransferRole::Borrow,
            )],
            vec![],
        ));
    }
    let viewed = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        format!("view_level_{:04}", depth - 1),
        vec![ProgramExpression::Value(ProgramValue::pointer(data))],
        vec![ProgramType::Int32Pointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    definitions.push(CompositeResourceDefinition::new(
        "viewed_return",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            )),
            viewed,
        ],
        vec![],
    ));
    definitions.sort_by(|a, b| a.name().cmp(b.name()));
    definitions
}

#[test]
fn viewed_children_keep_ownership_incremental_without_acquiring_ownership_origins() {
    let facts = PureFactContext::new();
    let own = Address::symbolic(Variable(8_819_400));
    let (_, entry, post, data) = super::fresh_allocation_tests::allocated_call(16);
    for depth in [1, 4] {
        let definitions = viewed_child_definitions(data.clone(), depth);
        let head = ResourceFact::own_composite(
            "viewed_return".into(),
            vec![ProgramValue::pointer(own.clone())],
        );
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(head, ReturnOwnershipOrigin::EntryBorrow, &facts)
            .unwrap();
        for composition in [
            ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
            ReturnResourceComposition::BodyReturn {
                state: &post,
                frame: entry.resources(),
                allocations: Some((
                    entry.population_effects.creation.as_ref().unwrap(),
                    post.population_effects.creation.as_ref().unwrap(),
                )),
                consumed: &ConsumedCellReturns::default(),
            },
        ] {
            let bodies = ConstructedReturnBodies::try_construct(
                &evaluated,
                &definitions,
                &post,
                composition,
                &facts,
            )
            .unwrap();
            assert!(!bodies.0.is_empty());
            let body = bodies.get(evaluated.occurrences[0].source).unwrap();
            assert_eq!(body.expansion.len(), 2);
            assert!(body.expansion.contains(&owner(own.clone(), 0, 1)));
            assert!(
                body.expansion
                    .contains(&ResourceFact::view_memory(MemoryRange::new(
                        data.clone(),
                        0u32.into(),
                        1u32.into()
                    )))
            );
            assert_eq!(body.viewed_children.len(), 1);
            let viewed = body
                .transfers
                .iter()
                .filter(|child| child.fact.is_view())
                .collect::<Vec<_>>();
            assert_eq!(viewed.len(), depth + 1);
            assert!(
                viewed
                    .iter()
                    .all(|child| child.origin == ReturnOwnershipOrigin::Description)
            );
            assert_eq!(body.viewed_children[0].1, viewed[0].source);
            for pair in viewed.windows(2) {
                assert_eq!(pair[1].parent, pair[0].source);
            }
            let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
                data.clone(),
                0,
                1,
            ));
            frame.synchronize_memory_equalities(&facts);
            assert!(matches!(
                frame.admit_returned_frontier(body.boundary(), &facts),
                FlatBodyAdmission::Admitted
            ));
            let (destination, transfers) = evaluated
                .restore_entry_borrows(ResourceContext::new(), composition, &facts)
                .unwrap()
                .finish(&facts)
                .unwrap();
            let projected = project_return_resource_cores(
                &evaluated.resources,
                &transfers,
                &bodies,
                &facts,
                &destination,
            );
            assert_eq!(
                projected[0].viewed_children.as_slice(),
                &body.viewed_children
            );
            assert_eq!(projected[0].destination, transfers[0].destination);
        }
    }
}

pub(super) fn selected_view_expansion_fixture() -> (
    ResourceContext,
    ResourceFact,
    ResourceOccurrenceId,
    LoanViewBinding,
    Vec<CompositeResourceDefinition>,
    SymbolicMemory,
) {
    selected_view_expansion_fixture_with_cells(1)
}

fn selected_view_expansion_fixture_with_cells(
    cells: u32,
) -> (
    ResourceContext,
    ResourceFact,
    ResourceOccurrenceId,
    LoanViewBinding,
    Vec<CompositeResourceDefinition>,
    SymbolicMemory,
) {
    use crate::kernel::program_expression::{int32_literal, variable};
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_401));
    let head = ResourceFact::view_composite(
        "selected_view".into(),
        vec![ProgramValue::pointer(pointer.clone())],
    );
    let owner = ResourceFact::own_composite(
        "selected_view".into(),
        vec![ProgramValue::pointer(pointer.clone())],
    );
    let ledger = LoanLedger::new();
    let caller = ledger.fresh_participant().unwrap();
    let callee = ledger.fresh_participant().unwrap();
    let input = CheckedResourceFact {
        fact: head.clone(),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    let (caller_resources, owned) =
        ResourceContext::new().unchecked_with_facts_and_occurrences([owner.clone()]);
    // The fixture's declared body is exactly these disjoint cells. Supply
    // the typed composite backing required by the ordinary loan planner.
    let backing = CompositeLoanBacking::from_checked_expansion(
        owned[0].1,
        owner,
        (0..cells)
            .map(|index| {
                ResourceFact::own_memory(MemoryRange::new(
                    pointer.clone(),
                    index.into(),
                    (index + 1).into(),
                ))
            })
            .collect(),
    )
    .unwrap();
    let plan = crate::kernel::loans::plan_stable_view_transfer_with_bindings_and_composites(
        &caller_resources,
        &[input],
        &facts,
        &ledger,
        caller,
        callee,
        &LoanViewBindings::default(),
        &BTreeMap::from([(owned[0].1, backing)]),
    )
    .unwrap();
    let source = plan
        .callee_resources
        .view_occurrences_for_fact(&head, &facts)[0];
    let binding = plan.callee_view_bindings().get(&source).unwrap().clone();
    let context = plan
        .callee_resources
        .clone()
        .with_loan_dependency(source, binding.clone());
    let definitions = vec![CompositeResourceDefinition::new(
        "selected_view",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        (0..cells)
            .map(|index| {
                ResourceSpec::owned_memory(MemorySegment::new(
                    variable("p"),
                    int32_literal(index),
                    int32_literal(index + 1),
                ))
            })
            .collect(),
        vec![],
    )];
    (
        context,
        head,
        source,
        binding,
        definitions,
        SymbolicMemory::new().with_block(pointer.base, cells * 4),
    )
}

#[test]
fn viewed_expansion_transports_only_the_selected_occurrence_dependency() {
    let facts = PureFactContext::new();
    let (parent, head, source, binding, definitions, memory) = selected_view_expansion_fixture();
    let (parent, extra) = parent.unchecked_with_facts_and_occurrences([head.clone()]);
    for (selected, bound) in [(source, true), (extra[0].1, false)] {
        let body = construct_composite_resource_body(
            &parent,
            &head,
            &definitions,
            &crate::kernel::ProgramPoint::of_memory(&memory),
            &facts,
            Some(selected),
            None,
        )
        .unwrap();
        let (piece, occurrence) = &body.occurrences[0];
        assert!(piece.is_view());
        let expected = LoanViewBinding {
            viewed: piece.clone(),
            ..binding.clone()
        };
        assert_eq!(
            body.expanded.loan_dependency(*occurrence),
            if bound { Some(&expected) } else { None }
        );
        assert!(parent.view_fact_for_occurrence(selected).is_some());
    }
}

pub(in crate::kernel::functions) fn returned_hold_fixture(
    count: usize,
) -> (ResourceContext, Vec<crate::kernel::loans::EscapedHold>) {
    let (resources, holds, _, _) = returned_hold_fixture_with_ledger(count);
    (resources, holds)
}

pub(in crate::kernel::functions) fn returned_hold_fixture_with_ledger(
    count: usize,
) -> (
    ResourceContext,
    Vec<crate::kernel::loans::EscapedHold>,
    LoanLedger,
    crate::kernel::loans::LoanParticipantId,
) {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_402));
    let range = MemoryRange::new(pointer, 0u32.into(), 1u32.into());
    let input = CheckedResourceFact {
        fact: ResourceFact::view_memory(range.clone()),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    let ledger = LoanLedger::new();
    let caller = ledger.fresh_participant().unwrap();
    let callee = ledger.fresh_participant().unwrap();
    let plan = crate::kernel::loans::plan_stable_view_transfer(
        &ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range)),
        &[input],
        &facts,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let head = ResourceFact::own_composite("returned_view".into(), vec![]);
    let (resources, inserted) = ResourceContext::new()
        .unchecked_with_facts_and_occurrences(std::iter::repeat_n(head, count));
    let escaping = BTreeMap::from([(
        plan.stable_views()[0].loan,
        inserted
            .into_iter()
            .map(|(head, occurrence)| crate::kernel::loans::EscapingComposite { head, occurrence })
            .collect(),
    )]);
    let recovered = plan.recover_stable_views(&facts, &escaping, &[]).unwrap();
    (resources, recovered.escaped_holds, recovered.ledger, caller)
}

#[test]
fn selected_view_expansion_keeps_raw_child_bindings_through_adjacent_normalization() {
    let facts = PureFactContext::new();
    let (context, head, selected, binding, definitions, memory) =
        selected_view_expansion_fixture_with_cells(2);
    let body = construct_composite_resource_body(
        &context,
        &head,
        &definitions,
        &crate::kernel::ProgramPoint::of_memory(&memory),
        &facts,
        Some(selected),
        None,
    )
    .unwrap();
    assert_eq!(
        body.children.len(),
        1,
        "the normalized group merges adjacent descriptions"
    );
    assert_eq!(
        body.occurrences.len(),
        2,
        "the producer retains both raw child identities"
    );
    for (piece, source) in body.occurrences {
        let dependency = body.expanded.loan_dependency(source).unwrap();
        assert_eq!(dependency.loan, binding.loan);
        assert_eq!(dependency.support, binding.support);
        assert_eq!(dependency.viewed, piece);
    }
}

#[test]
fn packaged_views_keep_normalized_descriptions_and_the_raw_source_group() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_819_403));
    let definition = CompositeResourceDefinition::new(
        "adjacent_views",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            ResourceSpec::viewed_memory(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            )),
            ResourceSpec::viewed_memory(MemorySegment::new(
                variable("p"),
                int32_literal(1),
                int32_literal(2),
            )),
        ],
        vec![],
    );
    let head = ResourceFact::own_composite(
        "adjacent_views".into(),
        vec![ProgramValue::pointer(pointer.clone())],
    );
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(head, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let state = ExecutionState::new();
    let bodies = ConstructedReturnBodies::construct(&evaluated, &[definition], &state, &facts);
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert_eq!(body.viewed_children.len(), 2);
    let (destination, transfers) = evaluated
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    let projected = project_return_resource_cores(
        &evaluated.resources,
        &transfers,
        &bodies,
        &facts,
        &destination,
    );
    let pieces = projected[0].constructed_borrowing_pieces();
    assert_eq!(pieces.len(), 1);
    assert_eq!(
        pieces[0].piece,
        ResourceFact::view_memory(MemoryRange::new(pointer, 0u32.into(), 2u32.into()))
    );
    assert_eq!(
        pieces[0].sources.as_ref(),
        &body
            .viewed_children
            .iter()
            .map(|(_, source)| *source)
            .collect::<Vec<_>>()
    );
    assert_eq!(pieces[0].support.occurrence, transfers[0].destination);
}

#[test]
fn escrow_boundary_checks_live_new_outputs_but_not_removed_occurrences() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address {
        base: "escrow-boundary".into(),
        offset: AddressOffset::Constant(0),
    };
    let escrow = owner(pointer.clone(), 0, 8);
    let protected = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(escrow);
    let overlap = owner(pointer.clone(), 4, 12);
    let separate = owner(pointer, 8, 12);
    for (output, succeeds) in [(overlap, false), (separate, true)] {
        let (live, emitted) = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts_and_occurrences([output.clone()]);
        let mut boundary = EscrowRecoveryBoundary::default();
        boundary.record(emitted[0].1, vec![output], vec![]);
        let empty = ResourceContext::new_with_equalities(&facts);
        let _fast = crate::kernel::search::FastOperationScope::enter("escrow boundary test");
        assert_eq!(
            boundary.admit(&protected, false, &live, &facts).is_ok(),
            succeeds
        );
        assert!(boundary.admit(&protected, false, &empty, &facts).is_ok());
    }
}

#[test]
fn escrow_boundary_checks_body_frontiers_against_released_inherited_holds() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address {
        base: "inherited-escrow-boundary".into(),
        offset: AddressOffset::Constant(0),
    };
    let inherited = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
        pointer.clone(),
        0,
        8,
    ));
    let head = ResourceFact::own_token("emitted-body".into(), vec![]);
    let (live, emitted) =
        ResourceContext::new_with_equalities(&facts).unchecked_with_facts_and_occurrences([head]);
    let mut boundary = EscrowRecoveryBoundary::default();
    boundary.record(emitted[0].1, vec![], vec![owner(pointer, 4, 12)]);
    let empty = ResourceContext::new_with_equalities(&facts);
    assert!(boundary.admit(&empty, false, &live, &facts).is_ok());
    assert!(boundary.admit(&inherited, false, &live, &facts).is_err());
}

#[test]
fn escrow_recovery_uses_the_lend_time_frontier_of_a_folded_owner() {
    use crate::kernel::loans::{
        CompositeLoanBacking, LoanLedger, LoanViewBindings,
        plan_stable_view_transfer_with_bindings_and_composites,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let pointer = Address {
        base: "folded-escrow".into(),
        offset: AddressOffset::Constant(0),
    };
    let piece = owner(pointer.clone(), 0, 8);
    let head = ResourceFact::own_composite("protected".into(), vec![]);
    let caller = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(head.clone());
    let source = caller.unique_owned_occurrence_for_fact(&head).unwrap().0;
    let ledger = LoanLedger::new();
    let lender = ledger.fresh_participant().unwrap();
    let borrower = ledger.fresh_participant().unwrap();
    let request = CheckedResourceFact {
        fact: ResourceFact::view_composite("protected".into(), vec![]),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    for (frontier, opaque) in [
        (vec![piece.clone()], false),
        (
            vec![ResourceFact::own_composite("opaque-child".into(), vec![])],
            true,
        ),
    ] {
        let backings = BTreeMap::from([(
            source,
            CompositeLoanBacking::from_checked_expansion(source, head.clone(), frontier).unwrap(),
        )]);
        let plan = plan_stable_view_transfer_with_bindings_and_composites(
            &caller,
            std::slice::from_ref(&request),
            &facts,
            &ledger,
            lender,
            borrower,
            &LoanViewBindings::default(),
            &backings,
        )
        .unwrap();
        let recovery = plan
            .recover_stable_views(&facts, &BTreeMap::new(), &[])
            .unwrap();
        for (output, expected) in [
            (owner(pointer.clone(), 4, 12), false),
            (owner(pointer.clone(), 8, 12), !opaque),
        ] {
            let (live, emitted) = ResourceContext::new_with_equalities(&facts)
                .unchecked_with_facts_and_occurrences([output.clone()]);
            let mut boundary = EscrowRecoveryBoundary::default();
            boundary.record(emitted[0].1, vec![output], vec![]);
            let restored = recovery.restore_returned_escrows(live, &boundary, &facts);
            assert_eq!(restored.is_ok(), expected);
            if let Ok((restored, _)) = restored {
                assert_eq!(restored.owned_fact_for_occurrence(source), Some(&head));
            }
        }
    }
}

#[test]
fn an_opaque_return_frontier_cannot_hide_new_ownership_from_escrow() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let protected = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
        Address::symbolic(Variable(8_919_999)),
        0,
        1,
    ));
    let head = ResourceFact::own_composite("opaque-return".into(), vec![]);
    let (live, emitted) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([head.clone()]);
    let mut boundary = EscrowRecoveryBoundary::default();
    boundary.record(emitted[0].1, vec![], vec![head]);
    assert!(boundary.admit(&protected, false, &live, &facts).is_err());
    assert!(
        boundary
            .admit(
                &ResourceContext::new_with_equalities(&facts),
                false,
                &live,
                &facts
            )
            .is_ok()
    );
}

#[test]
fn fact_only_view_expansion_keeps_ambient_child_identity_and_binding() {
    let facts = PureFactContext::new();
    let (parent, head, source, binding, definitions, memory) = selected_view_expansion_fixture();
    let at = crate::kernel::ProgramPoint::of_memory(&memory);
    let first = construct_composite_resource_body(
        &parent,
        &head,
        &definitions,
        &at,
        &facts,
        Some(source),
        None,
    )
    .unwrap();
    let child = first.raw_children[0].clone();
    let (parent, ambient) =
        parent.unchecked_with_facts_and_occurrences([child.clone(), head.clone()]);
    for choice in [None, Some(source)] {
        let body = construct_composite_resource_body(
            &parent,
            &head,
            &definitions,
            &at,
            &facts,
            choice,
            None,
        )
        .unwrap();
        let emitted = body.occurrences[0].1;
        assert_ne!(emitted, ambient[0].1);
        assert_eq!(
            body.expanded.view_fact_for_occurrence(ambient[0].1),
            Some(&child)
        );
        assert!(body.expanded.loan_dependency(ambient[0].1).is_none());
        assert_eq!(
            body.expanded.loan_dependency(emitted),
            Some(&LoanViewBinding {
                viewed: child.clone(),
                ..binding.clone()
            })
        );
        assert!(
            body.expanded
                .view_fact_for_occurrence(ambient[1].1)
                .is_some()
        );
        assert!(body.expanded.view_fact_for_occurrence(source).is_none());
    }
}

#[test]
fn cached_composite_expansion_reuses_symbolic_endpoint_fragments() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::symbolic(Variable(9_831_200));
    let end = MachineTerm::Variable(Variable(9_831_201));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(2u32.into(), end.clone()),
        true,
    );
    let owned = |start, end| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            pointer.clone(),
            start,
            end,
            1,
        ))
    };
    let left = owned(0u32.into(), 2u32.into());
    let right = owned(2u32.into(), end.clone());
    let whole = owned(0u32.into(), end);
    let head = ResourceFact::own(Resource::Composite {
        name: "cached_symbolic_cell".into(),
        arguments: Vec::new().into(),
    });
    let (context, kept) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([left.clone(), right.clone()]);
    let context = context
        .unchecked_with_fact(head.clone())
        .with_cached_supported_expansion(&head, vec![whole.clone()]);
    context.synchronize_memory_equalities(&facts);
    let at = ExecutionState::new().program_point();
    let expanded = expand_all_composite_resource_facts(&context, &[], &at, &facts).unwrap();
    assert_eq!(expanded.owned_fact_for_occurrence(kept[0].1), Some(&left));
    assert_eq!(expanded.owned_fact_for_occurrence(kept[1].1), Some(&right));
    assert!(!expanded.contains_exact_representation(&whole));
}
