use super::*;

fn owner(pointer: Pointer, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(pointer, start.into(), end.into()))
}

#[test]
fn mixed_composition_restores_symbolic_borrows_and_keeps_emitted_occurrence_order() {
    let facts = PureFactContext::new();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(8_810_000)),
    };
    let borrow = owner(pointer.clone(), 0, 1);
    let produced = owner(Pointer::symbolic(Variable(8_810_001)), 0, 1);
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
            |evaluated, (fact, entry_borrow)| evaluated.admit(fact, entry_borrow, &facts).unwrap(),
        );
        let _operation =
            crate::kernel::search::FastOperationScope::enter("mixed return composition");
        let prepared = evaluated
            .restore_entry_borrows(
                parent.clone(),
                ReturnResourceComposition::RestoreEntryBorrows,
                &facts,
            )
            .unwrap();
        assert!(prepared.frame.contains_exact_representation(&borrow));
        assert_eq!(prepared.pending.facts(), &[produced.clone()]);
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
    let borrow = owner(Pointer::symbolic(Variable(8_810_010)), 0, 1);
    let parent = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(borrow.clone());
    parent.synchronize_memory_equalities(&facts);
    let descriptions = EvaluatedReturnResources::new(&facts)
        .admit(borrow, true, &facts)
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
            .admit(ticket.clone(), borrowed_first, &facts)
            .unwrap()
            .admit(ticket.clone(), !borrowed_first, &facts)
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
                    ReturnResourceComposition::RestoreEntryBorrows,
                    &facts,
                )
                .unwrap();
            let restored = prepared.restored[0].1;
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
                &[],
                &state,
                &facts,
                &destination,
            )
            .unwrap();
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
    pointer: Pointer,
    caller: ResourceContext,
    facts: &PureFactContext,
) -> FunctionResourceTransfer {
    let state = ExecutionState::new()
        .with_memory(Memory::new().with_block(pointer.block.clone(), 1024))
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
    let pointer = Pointer::symbolic(Variable(8_860_000));
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
        .consumed_cell_return
        .expect("explicit scalar transfer");
    assert_eq!(
        caller.owned_fact_for_occurrence(selected.input),
        Some(&cell)
    );
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(cell.clone(), false, &facts)
        .unwrap();
    for _ in 0..2 {
        let (result, mapping) = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::RestoreConsumedCell(selected),
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
        assert_eq!(remaining.facts(), &[held.clone()]);
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
    let pointer = Pointer::symbolic(Variable(8_860_010));
    for (start, end) in [(1, 2), (0, 2)] {
        let caller = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts([owner(pointer.clone(), 0, 1), owner(pointer.clone(), 1, 2)]);
        let function = scalar_transfer_contract(MemorySegment::new(
            variable("p"),
            int32_literal(start),
            int32_literal(end),
        ));
        let transfer = prepare_scalar_transfer(&function, pointer.clone(), caller, &facts);
        assert!(transfer.consumed_cell_return.is_none());
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                owner(pointer.clone(), start as u32, end as u32),
                false,
                &facts,
            )
            .unwrap();
        assert!(
            evaluated
                .restore_entry_borrows(
                    transfer.caller_resources_after_requirements,
                    ReturnResourceComposition::RestoreEntryBorrows,
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
    let pointer = Pointer::symbolic(Variable(8_860_020));
    let function = scalar_transfer_contract(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ));
    let cell = owner(pointer.clone(), 0, 1);
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(pointer.block.clone(), 8))
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
        .admit(cell, false, &facts)
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
        let original = Pointer::symbolic(Variable(8_860_030));
        let returned = if alias {
            Pointer::symbolic(Variable(8_860_031))
        } else {
            original.clone()
        };
        let facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(original.clone(), returned.clone()),
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
        let selected = transfer.consumed_cell_return.expect("selected flat slice");
        let cell = owner(returned.clone(), 0, 1);
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(cell.clone(), false, &facts)
            .unwrap();
        let (result, mapping) = evaluated
            .restore_entry_borrows(
                transfer.caller_resources_after_requirements.clone(),
                ReturnResourceComposition::RestoreConsumedCell(selected),
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
fn consumed_scalar_transfer_declines_extra_outputs_and_entry_borrows() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(8_860_040));
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
    for unsupported in [
        function
            .clone()
            .with_resource_summary(vec![input.clone()], vec![output.clone(), output]),
        function.with_resource_summary(
            vec![input.clone().with_role(ResourceTransferRole::Borrow)],
            vec![
                input
                    .with_role(ResourceTransferRole::Borrow)
                    .with_state_source(ResourceStateSource::Entry),
            ],
        ),
    ] {
        let transfer =
            prepare_scalar_transfer(&unsupported, pointer.clone(), caller.clone(), &facts);
        assert!(transfer.consumed_cell_return.is_none());
    }
}
