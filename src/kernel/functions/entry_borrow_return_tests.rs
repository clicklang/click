use super::*;

#[test]
fn returned_borrows_keep_checked_entry_arguments_when_clauses_are_reordered() {
    let field = |name: &str| {
        let address = Pointer {
            block: format!("parent:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::Value(ProgramValue::pointer(address))),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        }
    };
    let clause = |name: &str| {
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "child_ref".into(),
            vec![field(name)],
            vec![ProgramType::Int32Pointer],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let left = clause("left");
    let right = clause("right");
    let function = program_function(ProgramType::Void, "borrow", Vec::new(), program_skip())
        .with_resource_summary(vec![left.clone(), right.clone()], vec![right, left]);
    let children = ["child:left", "child:right"].map(|name| {
        ResourceFact::own_composite(
            "child_ref".into(),
            vec![ProgramValue::pointer(Pointer {
                block: name.into(),
                offset: PointerOffsetTerm::Constant(0),
            })],
        )
    });
    let checked = children
        .iter()
        .enumerate()
        .map(|(index, fact)| CheckedResourceFact {
            fact: fact.clone(),
            role: ResourceTransferRole::Borrow,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: Some(index),
            selected_mutex_source: None,
        })
        .collect::<Vec<_>>();
    // Neither field has a materialized cell. Re-evaluating either return
    // clause would fail, even though its exact borrowed owner was checked.
    let state = ExecutionState::new();
    let returned = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &checked,
        &[],
        &state,
        &state,
        2,
        &[],
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        returned.resources.facts(),
        &[children[1].clone(), children[0].clone()]
    );
}

fn mixed_memory_contract(composite: bool, produced_first: bool) -> ProgramFunction {
    use crate::kernel::program_expression::{int32_literal, variable};
    let segment = |name| MemorySegment::new(variable(name), int32_literal(0), int32_literal(1));
    let borrowed = ResourceSpec::owned_memory(segment("p"))
        .with_role(ResourceTransferRole::Borrow)
        .with_state_source(ResourceStateSource::Entry);
    let produced = if composite {
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "mixed_box".into(),
            vec![variable("q")],
            vec![ProgramType::Int32Pointer],
            ResourceTransferRole::Produce,
            ResourceStateSource::Post,
        )
        .unwrap()
    } else {
        ResourceSpec::owned_memory(segment("q"))
            .with_role(ResourceTransferRole::Produce)
            .with_state_source(ResourceStateSource::Post)
    };
    let outputs = if produced_first {
        vec![produced, borrowed.clone()]
    } else {
        vec![borrowed.clone(), produced]
    };
    program_function(
        ProgramType::Void,
        "mixed_return",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        program_skip(),
    )
    .with_resource_summary(vec![borrowed], outputs)
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "mixed_box",
        vec![program_parameter("q", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment("q"))],
        vec![],
    )])
}

fn run_mixed_call(
    composite: bool,
    produced_first: bool,
    overlap: bool,
) -> (ExecutionState, Vec<FunctionPath>) {
    let pointer = Pointer::symbolic(Variable(8_800_000));
    let held =
        ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0u32.into(), 1u32.into()));
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(pointer.block.clone(), 8))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
    let function = mixed_memory_contract(composite, produced_first);
    let environment =
        ExecutionEnvironment::new().with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: function.clone(),
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let output = if overlap {
        pointer.clone()
    } else {
        pointer.offset_by_bytes(4)
    };
    let paths = execute_program_function_call_paths(
        &state,
        &function,
        &[
            crate::kernel::program_expression::pointer_value(pointer),
            crate::kernel::program_expression::pointer_value(output),
        ],
        &PureFactContext::new(),
        ExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .unwrap();
    (state, paths)
}

#[test]
fn mixed_produced_composite_cannot_overlap_a_restored_borrow() {
    for produced_first in [false, true] {
        let (_, paths) = run_mixed_call(true, produced_first, true);
        assert!(
            matches!(
                paths.as_slice(),
                [FunctionPath {
                    outcome: FunctionOutcome::RuntimeError(
                        RuntimeError::ProducedCompositeOverlapsHeldResource { .. }
                    ),
                    ..
                }]
            ),
            "mixed overlapping output was admitted: {paths:?}"
        );
    }
}

#[test]
fn mixed_adjacent_memory_and_composite_outputs_preserve_the_caller_borrow() {
    for composite in [false, true] {
        for produced_first in [false, true] {
            let (source, paths) = run_mixed_call(composite, produced_first, false);
            let [
                FunctionPath {
                    outcome: FunctionOutcome::Return { state, .. },
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("adjacent mixed return was refused: {paths:?}");
            };
            assert!(
                state
                    .resources()
                    .satisfies_fact(&source.resources().facts()[0], &PureFactContext::new(),)
            );
            assert_eq!(source.resources().facts().len(), 1);
        }
    }
}

#[test]
fn mixed_produced_flat_memory_cannot_duplicate_a_restored_borrow() {
    for produced_first in [false, true] {
        let (_, paths) = run_mixed_call(false, produced_first, true);
        assert!(matches!(
            paths.as_slice(),
            [FunctionPath {
                outcome: FunctionOutcome::RuntimeError(_),
                ..
            }]
        ));
    }
}

#[test]
fn return_roles_follow_skipped_guards_and_deferred_output_emission() {
    use crate::kernel::program_expression::{int32_literal, pointer_value, variable};
    let at = |id: u64| Pointer::symbolic(Variable(8_840_000 + id));
    let segment = |base| MemorySegment::new(base, int32_literal(0), int32_literal(1));
    let borrowed = ResourceSpec::owned_memory(segment(variable("unmaterialized_entry_name")))
        .with_role(ResourceTransferRole::Borrow)
        .with_state_source(ResourceStateSource::Entry);
    let false_guard = SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(int32_literal(0)),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(int32_literal(1)),
    };
    let field = at(0);
    let target = at(1);
    let held = ResourceFact::own_memory(MemoryRange::new(at(2), 0u32.into(), 1u32.into()));
    let target_read = ProgramExpression::TypedLoad {
        pointer: Box::new(pointer_value(field.clone())),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let produced_target = ResourceSpec::owned_memory(segment(target_read))
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
    let produced_field = ResourceSpec::owned_memory(MemorySegment::new(
        pointer_value(field.clone()),
        int32_literal(0),
        int32_literal(2),
    ))
    .with_role(ResourceTransferRole::Produce)
    .with_state_source(ResourceStateSource::Post);
    let function = program_function(
        ProgramType::Void,
        "deferred_mixed_return",
        vec![],
        program_skip(),
    )
    .with_resource_summary(
        vec![borrowed.clone()],
        vec![
            produced_target,
            borrowed.clone().with_guard(false_guard),
            borrowed,
            produced_field,
        ],
    );
    let checked = [CheckedResourceFact {
        fact: held.clone(),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: Some(0),
        selected_mutex_source: None,
    }];
    let state = ExecutionState::new().with_memory(
        Memory::new()
            .with_block(field.block.clone(), C_POINTER_BYTE_WIDTH)
            .with_block(target.block.clone(), 4)
            .store(field, ProgramValue::pointer(target)),
    );
    let returned = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &checked,
        &checked,
        &state,
        &state,
        4,
        &[],
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(returned.resources.facts().len(), 3);
    assert_eq!(returned.resources.facts()[0], held);
    assert_eq!(returned.entry_borrows, [true, false, false]);
}

#[test]
fn borrowed_composite_bodies_still_check_post_memory_against_the_retained_frame() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let field = Pointer::symbolic(Variable(8_850_000));
    let old_child = Pointer::symbolic(Variable(8_850_001));
    let retained_child = Pointer::symbolic(Variable(8_850_002));
    let field_value = ProgramValue::typed_pointer(field.clone(), ProgramType::Int32PointerPointer);
    let borrowed = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        "moving_box".into(),
        vec![ProgramExpression::Value(field_value.clone())],
        vec![ProgramType::Int32PointerPointer],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let segment = |base| MemorySegment::new(base, int32_literal(0), int32_literal(1));
    let child = ProgramExpression::TypedLoad {
        pointer: Box::new(variable("p")),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let function = program_function(ProgramType::Void, "moving_borrow", vec![], program_skip())
        .with_resource_summary(vec![borrowed.clone()], vec![borrowed])
        .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
            "moving_box",
            vec![program_parameter("p", ProgramType::Int32PointerPointer)],
            None,
            false,
            vec![
                ResourceSpec::owned_memory(segment(variable("p"))),
                ResourceSpec::owned_memory(segment(child)),
            ],
            vec![],
        )]);
    let held_borrow = ResourceFact::own_composite("moving_box".into(), vec![field_value]);
    let checked = [CheckedResourceFact {
        fact: held_borrow.clone(),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: Some(0),
        selected_mutex_source: None,
    }];
    let facts = PureFactContext::new();
    let frame =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new(retained_child.clone(), 0u32.into(), 1u32.into()),
        ));
    let memory = Memory::new()
        .with_block(field.block.clone(), C_POINTER_BYTE_WIDTH)
        .with_block(old_child.block.clone(), 4)
        .with_block(retained_child.block.clone(), 4)
        .store(field.clone(), ProgramValue::pointer(old_child));
    let entry = ExecutionState::new()
        .with_memory(memory.clone())
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held_borrow),
        );
    let post = entry
        .clone()
        .with_memory(memory.store(field, ProgramValue::pointer(retained_child)));
    let returned = evaluate_contract_return_resources(
        &frame,
        &[],
        &[],
        &checked,
        &checked,
        &entry,
        &post,
        "moving_borrow",
        function.contract_interface(),
        &[],
        ReturnResourceComposition::RestoreEntryBorrows,
        &facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert!(matches!(
        returned,
        Err(RuntimeError::ProducedCompositeOverlapsHeldResource { .. })
    ));
}

#[test]
fn unmatched_entry_borrow_descriptions_do_not_authorize_restoration() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let segment = |name| MemorySegment::new(variable(name), int32_literal(0), int32_literal(1));
    let borrowed = ResourceSpec::owned_memory(segment("p"))
        .with_role(ResourceTransferRole::Borrow)
        .with_state_source(ResourceStateSource::Entry);
    let produced = ResourceSpec::owned_memory(segment("q"))
        .with_role(ResourceTransferRole::Produce)
        .with_state_source(ResourceStateSource::Post);
    let function = program_function(
        ProgramType::Void,
        "unmatched_return",
        vec![],
        program_skip(),
    )
    .with_resource_summary(vec![], vec![borrowed, produced]);
    let p = Pointer::symbolic(Variable(8_860_000));
    let q = Pointer::symbolic(Variable(8_860_001));
    let facts = PureFactContext::new();
    let held = ResourceFact::own_memory(MemoryRange::new(p.clone(), 0u32.into(), 1u32.into()));
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held);
    frame.synchronize_memory_equalities(&facts);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(p.clone()))
        .with_local("q", ProgramValue::pointer(q.clone()))
        .with_memory(Memory::new().with_block(p.block, 4).with_block(q.block, 4));
    let evaluated = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &[],
        &[],
        &state,
        &state,
        2,
        &[],
        &facts,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(evaluated.entry_borrows, [false, false]);
    let prepared = evaluated
        .restore_entry_borrows(
            frame,
            ReturnResourceComposition::RestoreEntryBorrows,
            &facts,
        )
        .unwrap();
    assert!(matches!(
        prepared.finish(&facts),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));
}
