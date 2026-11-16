use super::*;
use crate::kernel::program_expression::{int32_literal, variable};

pub(super) fn named(
    pointer: Pointer,
    identity: u64,
) -> (ResourceFact, CompositeResourceDefinition) {
    let schema = ResourceFieldSchema::new(vec![(
        "tag".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(identity),
        "named_box".into(),
        vec![ProgramValue::pointer(pointer).into()].into(),
        schema.clone(),
        vec![ProgramValue::Int32(MachineTerm::constant(7)).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "named_box",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    )
    .with_instance_schema(Some(schema));
    (ResourceFact::own(Resource::Instance(instance)), definition)
}

fn emitted(fact: ResourceFact, facts: &PureFactContext) -> EvaluatedReturnResources {
    EvaluatedReturnResources::new(facts)
        .admit(fact, ReturnOwnershipOrigin::Description, facts)
        .unwrap()
}

pub(super) fn anchor(identity: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(identity)),
    }
}

pub(super) fn authority(pointer: Pointer, family: &str) -> ResourceFact {
    ResourceFact::own(Resource::PopulationAuthority(ResourceDescription::new(
        family.into(),
        vec![ProgramValue::pointer(pointer).into()].into(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    )))
}

pub(super) fn control(pointer: Pointer) -> (ResourceFact, CompositeResourceDefinition) {
    let member = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "member".into(),
        vec![variable("p")],
        vec![ProgramType::Int32Pointer],
    );
    let authority = ResourceSpec::new(
        ResourceTerm::PopulationAuthority {
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(member),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            population_arity: None,
            state_source: ResourceStateSource::Current,
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "control",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            )),
            authority,
        ],
        vec![],
    );
    (
        ResourceFact::own_composite("control".into(), vec![ProgramValue::pointer(pointer)]),
        definition,
    )
}

pub(super) fn ledger(pointer: Pointer) -> ExecutionState {
    let authority = authority(pointer, "member");
    ExecutionState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(authority.clone()))
        .import_opaque_population(&authority, 0)
        .unwrap()
}

pub(super) fn matched_type() -> AlgebraicType {
    let variants: Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Empty".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Full".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32Pointer)],
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "BoxModel".into(),
        arguments: vec![],
    };
    AlgebraicType {
        rigid: false,
        name: "BoxModel".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

pub(super) fn constructor(pointer: Pointer) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: matched_type(),
        node: AlgebraicTermNode::Constructor {
            variant: "Full".into(),
            fields: vec![ProgramValue::pointer(pointer).into()],
        },
    }
}

pub(super) fn matched(
    model: AlgebraicTerm,
    identity: u64,
) -> (ResourceFact, CompositeResourceDefinition) {
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(model.algebraic_type.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(identity),
        "matched_box".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let mut definition =
        CompositeResourceDefinition::new("matched_box", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: model.algebraic_type,
        arms: vec![
            ResourceMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
                variant: "Full".into(),
                bindings: vec!["ptr".into()],
                binding_types: vec![AlgebraicValueType::Program(ProgramType::Int32Pointer)],
                binding_variables: vec![None],
                contains: vec![
                    ResourceSpec::owned_memory(MemorySegment::new(
                        variable("ptr"),
                        int32_literal(0),
                        int32_literal(1),
                    )),
                    ResourceSpec::owned_memory(MemorySegment::new(
                        variable("ptr"),
                        int32_literal(2),
                        int32_literal(3),
                    )),
                ],
                facts: vec![],
                children: vec![],
            },
        ],
    });
    (ResourceFact::own(Resource::Instance(instance)), definition)
}

#[test]
fn named_instances_carry_exact_fields_occurrences_and_projection_without_definitions() {
    let facts = PureFactContext::new();
    let mut outputs = EvaluatedReturnResources::new(&facts);
    let pointer = Pointer::symbolic(Variable(8_870_000));
    let (head, definition) = named(pointer.clone(), 8_870_001);
    let (other, _) = named(Pointer::symbolic(Variable(8_870_002)), 8_870_003);
    outputs = outputs
        .admit(head.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap()
        .admit(other, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let state = ExecutionState::new();
    let bodies = ConstructedReturnBodies::construct(&outputs, &[definition], &state, &facts);
    assert!(bodies.1.is_empty());
    let mut children = BTreeSet::new();
    for occurrence in &outputs.occurrences {
        let body = bodies.get(occurrence.source).unwrap();
        let Resource::Instance(selected) = outputs
            .resources
            .owned_fact_for_occurrence(occurrence.source)
            .unwrap()
            .resource()
        else {
            unreachable!()
        };
        assert_eq!(
            body.specialized.as_ref().unwrap().instance.as_ref(),
            Some(selected)
        );
        assert!(children.insert(body.transfers[0].source));
        assert_eq!(body.transfers[0].parent, occurrence.source);
    }
    let (destination, transfers) = outputs
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    let projected = project_return_resource_cores(
        &outputs.resources,
        &transfers,
        &bodies,
        &[],
        &state,
        &facts,
        &destination,
    )
    .unwrap();
    assert_eq!(projected.len(), 2);
    assert_eq!(
        projected[0].expansion,
        bodies.get(outputs.occurrences[0].source).unwrap().expansion
    );
    let held = ResourceFact::own_memory(MemoryRange::new(pointer, 0u32.into(), 1u32.into()));
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held.clone());
    frame.synchronize_memory_equalities(&facts);
    let error = produced_composite_frontier_conflict(
        &frame,
        std::iter::once((&head, bodies.get(outputs.occurrences[0].source))),
        &[],
        state.memory(),
        &facts,
    );
    let Some(RuntimeError::ProducedCompositeOverlapsHeldResource { held: selected, .. }) = error
    else {
        panic!("named body must be checked against the frame");
    };
    assert_eq!(*selected, held);
}

#[test]
fn named_model_pointer_does_not_gain_parameter_borrow_custody() {
    let facts = PureFactContext::new();
    let pointer = Pointer::symbolic(Variable(8_870_010));
    let schema = ResourceFieldSchema::new(vec![(
        "address".into(),
        ResourceFieldType::Program(ProgramType::Int32Pointer),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(8_870_011),
        "model_pointer".into(),
        vec![].into(),
        schema.clone(),
        vec![ProgramValue::pointer(pointer).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "model_pointer",
        vec![],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("address"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own(Resource::Instance(instance)),
            ReturnOwnershipOrigin::EntryBorrow,
            &facts,
        )
        .unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &outputs,
        &[definition],
        &ExecutionState::new(),
        ReturnResourceComposition::RestoreEntryBorrows,
        &facts,
    )
    .unwrap();
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    assert_eq!(body.transfers[0].origin, ReturnOwnershipOrigin::Description);
    assert_eq!(body.boundary.len(), 1);
}

#[test]
fn named_fixed_memory_preserves_the_consumed_input_selected_at_entry() {
    let facts = PureFactContext::new();
    let pointer = Pointer::symbolic(Variable(8_870_020));
    let (head, definition) = named(pointer.clone(), 8_870_021);
    let schema = definition.instance_schema.clone().unwrap();
    let inner = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "named_box".into(),
        vec![variable("p")],
        vec![ProgramType::Int32Pointer],
    );
    let output = ResourceSpec::instance(
        Variable(8_870_022),
        "named_box".into(),
        schema,
        inner,
        ResourceTransferRole::Produce,
        ResourceStateSource::Post,
    )
    .unwrap();
    let input = ResourceSpec::owned_memory(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ))
    .with_role(ResourceTransferRole::Consume);
    let function = program_function(
        ProgramType::Void,
        "package_named",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        program_skip(),
    )
    .with_resource_summary(vec![input], vec![output])
    .with_composite_resource_definitions(vec![definition]);
    let caller = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
        ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0u32.into(), 1u32.into())),
    );
    let transfer = super::tests::prepare_scalar_transfer(&function, pointer, caller, &facts);
    assert_eq!(transfer.consumed_cell_returns.children.len(), 1);
    let selected = transfer.consumed_cell_returns.children[&vec![0, 0]];
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit_clause(head, ReturnOwnershipOrigin::Description, Some(0), &facts)
        .unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &outputs,
        function
            .contract_interface()
            .composite_resource_definitions(),
        &ExecutionState::new(),
        ReturnResourceComposition::ApplyTransfers(&transfer.consumed_cell_returns),
        &facts,
    )
    .unwrap();
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    assert_eq!(
        body.transfers[0].origin,
        ReturnOwnershipOrigin::ConsumedCell(selected)
    );
    assert!(body.boundary.is_empty());
}

#[test]
fn authority_returns_retain_ledger_counts_and_refuse_a_duplicate_held_authority() {
    let facts = PureFactContext::new();
    let pointer = anchor(8_870_030);
    let state = ledger(pointer.clone());
    let (head, definition) = control(pointer.clone());
    let outputs = emitted(head.clone(), &facts);
    let bodies =
        ConstructedReturnBodies::construct(&outputs, &[definition.clone()], &state, &facts);
    let source = outputs.occurrences[0].source;
    let body = bodies.get(source).unwrap();
    let evidence = body.specialized.as_ref().unwrap();
    assert_eq!(evidence.authorities.len(), 1);
    let held = authority(pointer.clone(), "member");
    let Resource::PopulationAuthority(description) = held.resource() else {
        unreachable!()
    };
    let expected = state
        .population_effects
        .creation
        .as_ref()
        .unwrap()
        .observe_symbolic(description)
        .unwrap()
        .entry_count;
    assert_eq!(evidence.authorities[0].1, expected);
    assert_eq!(evidence.authorities[0].0, body.transfers[1].source);
    let held = authority(pointer, "member");
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held.clone());
    let FlatBodyAdmission::Conflict { held: selected, .. } =
        frame.admit_returned_flat_body(body, &facts)
    else {
        panic!("authority must not duplicate across the boundary");
    };
    assert_eq!(*selected, held);
    assert!(
        ConstructedReturnBodies::try_construct(
            &outputs,
            &[definition.clone()],
            &ExecutionState::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        )
        .is_none()
    );
    let mut repeated = definition;
    repeated.contains.push(repeated.contains[1].clone());
    assert!(
        ConstructedReturnBodies::try_construct(
            &outputs,
            &[repeated],
            &state,
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        )
        .is_none()
    );
}

#[test]
fn authority_identity_cannot_be_recovered_through_a_pointer_alias() {
    let pointer = anchor(8_870_040);
    let alias = anchor(8_870_041);
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(pointer.clone(), alias.clone()),
        true,
    );
    let state = ledger(pointer);
    let (head, definition) = control(alias);
    let outputs = emitted(head, &facts);
    assert!(
        ConstructedReturnBodies::try_construct(
            &outputs,
            &[definition],
            &state,
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        )
        .is_none()
    );
}

#[test]
fn matched_returns_carry_one_selected_constructor_and_keep_unknown_models_opaque() {
    let pointer = Pointer::symbolic(Variable(8_870_050));
    let model = AlgebraicTerm {
        algebraic_type: matched_type(),
        node: AlgebraicTermNode::Variable(Variable(8_870_051)),
    };
    let selected = constructor(pointer);
    let (head, definition) = matched(model.clone(), 8_870_052);
    let parent = PureFactContext::new();
    let outputs = emitted(head, &parent);
    let source = outputs.occurrences[0].source;
    let bodies = ConstructedReturnBodies::construct(
        &outputs,
        &[definition.clone()],
        &ExecutionState::new(),
        &parent,
    );
    assert_eq!(bodies.get(source).unwrap().folded.len(), 1);
    assert!(bodies.get(source).unwrap().boundary.is_empty());
    let branch = parent.clone().assume_proposition(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(selected.clone()),
    ));
    let bodies = ConstructedReturnBodies::construct(
        &outputs,
        &[definition.clone()],
        &ExecutionState::new(),
        &branch,
    );
    let body = bodies.get(source).unwrap();
    assert_eq!(
        body.specialized.as_ref().unwrap().constructor.as_ref(),
        Some(&selected)
    );
    assert_eq!(body.transfers.len(), 2);
    assert!(body.viewed_children.is_empty());
    assert_eq!(body.transfers[1].origin, ReturnOwnershipOrigin::Description);
    assert!(body.transfers[1].fact.is_own());
    let (destination, transfers) = outputs
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &branch,
        )
        .unwrap()
        .finish(&branch)
        .unwrap();
    let projected = project_return_resource_cores(
        &outputs.resources,
        &transfers,
        &bodies,
        &[],
        &ExecutionState::new(),
        &branch,
        &destination,
    )
    .unwrap();
    assert_eq!(projected[0].expansion, body.expansion);
    assert!(
        projected[0]
            .constructed_borrowing_pieces()
            .unwrap()
            .is_empty()
    );
    let parent_bodies = ConstructedReturnBodies::construct(
        &outputs,
        &[definition],
        &ExecutionState::new(),
        &parent,
    );
    assert_eq!(parent_bodies.get(source).unwrap().folded.len(), 1);
}
