use super::*;
use crate::kernel::program_expression::{int32_literal, variable};

pub(super) fn allocated_call(
    bytes: u32,
) -> (ExecutionState, ExecutionState, ExecutionState, Pointer) {
    let held = Pointer::symbolic(Variable(8_930_000));
    let caller = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_block(held.block.clone(), 4)
                .store(held.clone(), int32(17)),
        )
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(held, 0u32.into(), 1u32.into())),
        ));
    let mut entry = caller
        .clone()
        .with_local("p", ProgramValue::pointer(Pointer::null()))
        .with_resource_context(ResourceContext::new());
    Arc::make_mut(&mut entry.population_effects).creation = caller
        .population_effects
        .creation
        .as_ref()
        .map(CreationEvents::enter_call);
    let statement = ProgramStatement::HeapAllocate {
        target: "p".into(),
        bytes: int32_literal(bytes),
        zeroed: false,
        object_type: None,
        ends_program_on_failure: true,
    };
    let paths = execute_execution_statement_paths(
        &entry,
        &statement,
        &PureFactContext::new(),
        ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    let [
        StatementExecutionPath {
            outcome: StatementOutcome::Normal(post),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation failed: {paths:?}")
    };
    let native = post.locals().get_native("p").unwrap();
    let ProgramValue::Pointer(pointer) = native.as_ref() else {
        panic!("allocator did not return a pointer")
    };
    let pointer = pointer.pointer().clone();
    (caller, entry, post.as_ref().clone(), pointer)
}

fn returned_specs(base: impl Into<BindingName>, cells: u32) -> Vec<ResourceSpec> {
    let base = base.into();
    vec![
        ResourceSpec::owned_memory(
            MemorySegment::new(
                variable(base.clone()),
                int32_literal(0),
                int32_literal(cells),
            )
            .with_uninitialized(true),
        )
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post),
        ResourceSpec::token(
            ResourceAccessMode::Own,
            ResourceFact::ALLOCATION_RESOURCE_NAME.into(),
            vec![variable(base), int32_literal(16)],
            vec![ProgramType::Int32Pointer, ProgramType::Int32],
        )
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post),
    ]
}

pub(super) fn fresh_return_facts(pointer: &Pointer, cells: u32) -> [ResourceFact; 2] {
    [
        ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0u32.into(), cells.into())),
        ResourceFact::own_allocation(pointer.clone(), 16),
    ]
}

#[test]
fn allocator_provenance_is_attached_to_each_emitted_ownership_occurrence() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let (caller, entry, post, pointer) = allocated_call(16);
    let creator = checked_allocation_creator(&caller, &entry).unwrap();
    let events = post.population_effects.creation.as_ref().unwrap();
    let function = program_function(ProgramType::Void, "fresh_returns", vec![], program_skip())
        .with_resource_summary(vec![], returned_specs("p", 4));
    let evaluated = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &[],
        &[],
        &entry,
        &post,
        2,
        &[],
        ReturnResourceComposition::BodyAllocations {
            consumed: None,
            creator: &creator,
            events,
        },
        &facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    let PointerBlock::Heap(identity) = pointer.block else {
        panic!("not a resolved allocation")
    };
    assert!(evaluated.occurrences.iter().all(|entry| entry.origin
        == ReturnOwnershipOrigin::FreshAllocation(FreshAllocationReturn {
            allocation: identity
        })));
    for _ in 0..2 {
        let (result, mappings) = evaluated
            .restore_entry_borrows(
                caller.resources().clone(),
                ReturnResourceComposition::BodyAllocations {
                    consumed: None,
                    creator: &creator,
                    events,
                },
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        assert_eq!(mappings.len(), 2);
        for (index, mapping) in mappings.iter().enumerate() {
            assert_eq!(mapping.fresh_allocation, Some(identity));
            assert_eq!(mapping.consumed_input, None);
            assert_eq!(mapping.source, evaluated.occurrences[index].source);
            assert_eq!(
                result.owned_fact_for_occurrence(mapping.destination),
                evaluated
                    .resources
                    .owned_fact_for_occurrence(mapping.source)
            );
        }
        assert!(result.contains_exact_representation(&caller.resources().facts()[0]));
    }
}

#[test]
fn an_allocation_claim_pending_result_and_an_older_call_are_not_fresh_returns() {
    let _session = crate::kernel::VerificationSession::enter();
    let (caller, entry, post, pointer) = allocated_call(16);
    let creator = checked_allocation_creator(&caller, &entry).unwrap();
    let events = post.population_effects.creation.as_ref().unwrap();
    for fact in fresh_return_facts(&pointer, 4) {
        assert!(FreshAllocationReturn::from_created_owner(&fact, &creator, events).is_some());
        assert!(
            FreshAllocationReturn::from_created_owner(
                &fact,
                caller.population_effects.creation.as_ref().unwrap(),
                events
            )
            .is_none()
        );
        assert!(FreshAllocationReturn::from_created_owner(&fact, &creator, &creator).is_none());
        let returned_events =
            events.return_to(caller.population_effects.creation.as_ref().unwrap());
        let later_call = returned_events.enter_call();
        assert!(
            FreshAllocationReturn::from_created_owner(&fact, &later_call, &returned_events)
                .is_none()
        );
        let retired = events.retired(&pointer.block).unwrap();
        assert!(FreshAllocationReturn::from_created_owner(&fact, &creator, &retired).is_none());
    }
    let pending = Pointer::symbolic(Variable(8_930_010));
    let pending_events = creator.pending_creation(pending.block.clone());
    let predicted = Pointer {
        block: PointerBlock::Heap(8_930_010),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(
        FreshAllocationReturn::from_created_owner(
            &ResourceFact::own_allocation(predicted, 16),
            &creator,
            &pending_events
        )
        .is_none()
    );
    assert!(
        FreshAllocationReturn::from_created_owner(
            &ResourceFact::own_allocation(pending, 16),
            &creator,
            &pending_events
        )
        .is_none()
    );
    assert!(checked_allocation_creator(&caller, &caller).is_none());
}

#[test]
fn raw_description_validation_does_not_exercise_a_fresh_allocation_annotation() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let (_, entry, post, pointer) = allocated_call(16);
    let creator = entry.population_effects.creation.as_ref().unwrap();
    let events = post.population_effects.creation.as_ref().unwrap();
    let fact = fresh_return_facts(&pointer, 4)[0].clone();
    let origin = FreshAllocationReturn::from_created_owner(&fact, creator, events).unwrap();
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            fact.clone(),
            ReturnOwnershipOrigin::FreshAllocation(origin),
            &facts,
        )
        .unwrap();
    let prepared = evaluated
        .restore_entry_borrows(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(fact),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(prepared.restored.is_empty());
    assert!(prepared.finish(&facts).is_err());
}

fn allocating_function(cells: u32) -> ProgramFunction {
    let body = program_seq(
        program_declare("p", ProgramType::Int32Pointer),
        program_seq(
            ProgramStatement::HeapAllocate {
                target: "p".into(),
                bytes: int32_literal(16),
                zeroed: false,
                object_type: None,
                ends_program_on_failure: true,
            },
            program_return(variable("p")),
        ),
    );
    program_function(ProgramType::Int32Pointer, "allocate_return", vec![], body)
        .with_resource_summary(vec![], returned_specs(CONTRACT_RESULT, cells))
}

#[test]
fn executed_allocator_returns_preserve_the_frame_and_check_actual_body_custody() {
    for cells in [4, 8] {
        let _session = crate::kernel::VerificationSession::enter();
        let (caller, _, _, _) = allocated_call(16);
        let function = allocating_function(cells);
        let paths = execute_program_function_call_paths(
            &caller,
            &function,
            &[],
            &PureFactContext::new(),
            ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        if cells == 4 {
            let [
                FunctionPath {
                    outcome: FunctionOutcome::Return { value, state },
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("fresh return failed: {paths:?}")
            };
            let pointer = value.pointer().unwrap().pointer();
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            for returned in fresh_return_facts(pointer, 4) {
                assert!(
                    state
                        .resources()
                        .satisfies_fact(&returned, &PureFactContext::new())
                );
            }
            assert!(
                state
                    .resources()
                    .contains_exact_representation(&caller.resources().facts()[0])
            );
        } else {
            assert!(
                matches!(paths.as_slice(), [FunctionPath { outcome: FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)), .. }]
                if message.contains("joint returned resource units")),
                "oversized return accepted: {paths:?}"
            );
        }
    }
}

#[test]
fn composite_children_use_only_actual_allocation_provenance() {
    let facts = PureFactContext::new();
    let (_, entry, post, pointer) = allocated_call(16);
    let (_, wrong_entry, _, _) = allocated_call(16);
    let definition = super::tests::flat_body_definition("created_body", &pointer, 2);
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own_composite("created_body".into(), vec![]),
            ReturnOwnershipOrigin::Description,
            &facts,
        )
        .unwrap();
    for (creator, fresh) in [
        (entry.population_effects.creation.as_ref().unwrap(), true),
        (
            wrong_entry.population_effects.creation.as_ref().unwrap(),
            false,
        ),
    ] {
        let bodies = ConstructedReturnBodies::try_construct(
            &evaluated,
            &[definition.clone()],
            &post,
            ReturnResourceComposition::BodyAllocations {
                consumed: None,
                creator,
                events: post.population_effects.creation.as_ref().unwrap(),
            },
            &facts,
        )
        .unwrap();
        let body = bodies.get(evaluated.occurrences[0].source).unwrap();
        assert_eq!(
            body.transfers
                .iter()
                .filter(|child| matches!(child.origin, ReturnOwnershipOrigin::FreshAllocation(_)))
                .count(),
            if fresh { 2 } else { 0 }
        );
        assert_eq!(
            body.owned_memory_frontier().count(),
            if fresh { 0 } else { 2 }
        );
    }
}

#[test]
fn executed_composite_allocation_returns_still_check_body_custody() {
    for cells in [4, 8] {
        let _session = crate::kernel::VerificationSession::enter();
        let (caller, _, _, _) = allocated_call(16);
        let function = allocating_function(cells)
            .with_resource_summary(
                vec![],
                vec![super::tests::composite_spec(
                    "allocated_body",
                    variable(CONTRACT_RESULT),
                    ResourceTransferRole::Produce,
                )],
            )
            .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
                "allocated_body",
                vec![program_parameter("p", ProgramType::Int32Pointer)],
                None,
                false,
                returned_specs("p", cells),
                vec![],
            )]);
        let paths = execute_program_function_call_paths(
            &caller,
            &function,
            &[],
            &PureFactContext::new(),
            ExecutionContext::execute_bodies(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(
            matches!(
                paths.as_slice(),
                [FunctionPath {
                    outcome: FunctionOutcome::Return { .. },
                    ..
                }]
            ),
            cells == 4,
            "{paths:?}"
        );
    }
}

#[test]
fn one_composite_can_mix_selected_consumed_and_fresh_children() {
    let facts = PureFactContext::new();
    let (_, entry, post, fresh) = allocated_call(16);
    let old = Pointer::symbolic(Variable(8_819_300));
    let mut definition = super::tests::nested_transfer_function(1)
        .contract_interface()
        .composite_resource_definitions()[0]
        .clone();
    definition
        .contains
        .push(ResourceSpec::owned_memory(MemorySegment::new(
            ProgramExpression::Value(ProgramValue::pointer(fresh)),
            int32_literal(0),
            int32_literal(1),
        )));
    let function = super::tests::nested_transfer_function(1)
        .with_composite_resource_definitions(vec![definition]);
    let caller = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
        ResourceFact::own_memory(MemoryRange::new(old.clone(), 0u32.into(), 1u32.into())),
    );
    let transfer = super::tests::prepare_scalar_transfer(&function, old.clone(), caller, &facts);
    let post = post.with_local("p", ProgramValue::pointer(old));
    let evaluated =
        super::tests::evaluate_mixed_scalar(&function, &post, &transfer, &facts).unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &evaluated,
        function
            .contract_interface()
            .composite_resource_definitions(),
        &post,
        ReturnResourceComposition::BodyAllocations {
            consumed: Some(&transfer.consumed_cell_returns),
            creator: entry.population_effects.creation.as_ref().unwrap(),
            events: post.population_effects.creation.as_ref().unwrap(),
        },
        &facts,
    )
    .unwrap();
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    assert!(matches!(
        body.transfers[0].origin,
        ReturnOwnershipOrigin::ConsumedCell(_)
    ));
    assert!(matches!(
        body.transfers[1].origin,
        ReturnOwnershipOrigin::FreshAllocation(_)
    ));
    assert!(body.boundary.is_empty());
}
