use super::tests::composite_spec;
use super::*;
use crate::kernel::program_expression::{cast, int32_literal, variable};

fn owner(pointer: Address, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(pointer, start.into(), end.into()))
}

pub(super) fn existential_definition(count: u32) -> CompositeResourceDefinition {
    let mut children = vec![ResourceSpec::owned_memory(MemorySegment::new(
        variable("p"),
        int32_literal(0),
        int32_literal(1),
    ))];
    children.extend((0..count).map(|index| {
        ResourceSpec::owned_memory(MemorySegment::new(
            variable("hidden"),
            int32_literal(index * 2),
            int32_literal(index * 2 + 1),
        ))
    }));
    let mut definition = CompositeResourceDefinition::new(
        "existential_return",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        children,
        vec![],
    );
    definition
        .witnesses
        .push(program_parameter("hidden", ProgramType::Int32Pointer));
    definition
}

pub(super) fn existential_outputs(
    pointer: Address,
    count: u32,
    facts: &PureFactContext,
) -> EvaluatedReturnResources {
    let mut evaluated = EvaluatedReturnResources::new(facts);
    for _ in 0..count {
        evaluated = evaluated
            .admit(
                ResourceFact::own_composite(
                    "existential_return".into(),
                    vec![ProgramValue::pointer(pointer.clone())],
                ),
                ReturnOwnershipOrigin::EntryBorrow,
                facts,
            )
            .unwrap();
    }
    evaluated
}

#[test]
fn existential_returns_carry_the_producers_witness_and_independent_child_ids() {
    let facts = PureFactContext::new();
    let evaluated = existential_outputs(Address::symbolic(Variable(8_850_000)), 2, &facts);
    let state = ExecutionState::new();
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[existential_definition(1)],
        &state,
        &facts,
    );
    assert!(!bodies.0.is_empty());
    let mut children = BTreeSet::new();
    for occurrence in &evaluated.occurrences {
        let body = bodies.get(occurrence.source).unwrap();
        let [ProgramValue::Pointer(hidden)] = body.witnesses[&occurrence.source].as_slice() else {
            panic!("one pointer witness");
        };
        assert_eq!(
            body.transfers[1].fact,
            owner(hidden.pointer().clone(), 0, 1)
        );
        assert_eq!(body.transfers[1].parent, occurrence.source);
        assert!(children.insert(body.transfers[1].source));
    }
    let (destination, transfers) = evaluated
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    // Consumers have no definitions and cannot bind the witness a second time.
    let projected = project_return_resource_cores(
        &evaluated.resources,
        &transfers,
        &bodies,
        &facts,
        &destination,
    )
    .unwrap();
    for (projection, occurrence) in projected.iter().zip(&evaluated.occurrences) {
        assert_eq!(
            projection.expansion,
            bodies.get(occurrence.source).unwrap().expansion
        );
    }
}

#[test]
fn existential_witness_memory_does_not_receive_parameter_borrow_custody() {
    let facts = PureFactContext::new();
    let evaluated = existential_outputs(Address::symbolic(Variable(8_850_001)), 1, &facts);
    let source = evaluated.occurrences[0].source;
    let bodies = ConstructedReturnBodies::try_construct(
        &evaluated,
        &[existential_definition(1)],
        &ExecutionState::new(),
        ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
        &facts,
    )
    .unwrap();
    let body = bodies.get(source).unwrap();
    assert_eq!(body.transfers[0].origin, ReturnOwnershipOrigin::EntryBorrow);
    assert_eq!(body.transfers[1].origin, ReturnOwnershipOrigin::Description);
    assert_eq!(body.boundary, vec![body.transfers[1].fact.clone()]);
    let held = body.boundary[0].clone();
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(held.clone());
    frame.synchronize_memory_equalities(&facts);
    let error = produced_composite_frontier_conflict(
        &frame,
        std::iter::once((
            evaluated
                .resources
                .owned_fact_for_occurrence(source)
                .unwrap(),
            Some(body),
        )),
        &facts,
    );
    let Some(RuntimeError::ProducedCompositeOverlapsHeldResource {
        piece,
        held: selected,
        ..
    }) = error
    else {
        panic!("a witness is not a transfer");
    };
    assert_eq!(*piece, held);
    assert_eq!(*selected, held);
}

#[test]
fn viewed_existential_children_keep_their_binding_and_never_gain_owned_custody() {
    let facts = PureFactContext::new();
    for access in [ResourceAccessMode::Own, ResourceAccessMode::View] {
        let child = ResourceSpec::declared(
            ResourceFamily::Composite,
            access,
            "existential_return".into(),
            vec![variable("p")],
            vec![ProgramType::Int32Pointer],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap();
        let parent = CompositeResourceDefinition::new(
            "wrapper",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            vec![child],
            vec![],
        );
        let evaluated = EvaluatedReturnResources::new(&facts)
            .admit(
                ResourceFact::own_composite(
                    "wrapper".into(),
                    vec![ProgramValue::pointer(Address::symbolic(Variable(
                        8_850_002,
                    )))],
                ),
                ReturnOwnershipOrigin::EntryBorrow,
                &facts,
            )
            .unwrap();
        let bodies = ConstructedReturnBodies::try_construct(
            &evaluated,
            &[existential_definition(1), parent],
            &ExecutionState::new(),
            ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
            &facts,
        )
        .unwrap();
        let body = bodies.get(evaluated.occurrences[0].source).unwrap();
        let child = &body.transfers[0];
        assert!(body.witnesses.contains_key(&child.source));
        assert_eq!(body.transfers[2].parent, child.source);
        assert_eq!(body.transfers[2].origin, ReturnOwnershipOrigin::Description);
        assert_eq!(
            body.transfers[2].fact.is_view(),
            access == ResourceAccessMode::View
        );
        assert_eq!(
            body.boundary.iter().any(ResourceFact::is_own),
            access == ResourceAccessMode::Own
        );
    }
}

#[test]
fn unsupported_existentials_refuse_and_migrated_failures_do_not_retry() {
    let facts = PureFactContext::new();
    let evaluated = existential_outputs(Address::symbolic(Variable(8_850_003)), 1, &facts);
    let source = evaluated.occurrences[0].source;
    for variant in 0..3 {
        let mut definition = existential_definition(1);
        match variant {
            0 => definition
                .witnesses
                .push(program_parameter("second", ProgramType::Int32Pointer)),
            1 => definition.contains.push(composite_spec(
                "existential_return",
                variable("hidden"),
                ResourceTransferRole::Borrow,
            )),
            _ => definition.witnesses = vec![program_parameter("hidden", ProgramType::Int32)],
        }
        let bodies = ConstructedReturnBodies::try_construct(
            &evaluated,
            &[definition],
            &ExecutionState::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        );
        if variant == 0 {
            assert_eq!(
                bodies.unwrap().get(source).unwrap().witnesses[&source].len(),
                2
            );
        } else {
            assert!(bodies.is_none());
        }
    }

    let mut invalid = existential_definition(1);
    invalid.contains.push(invalid.contains[1].clone());
    assert!(
        ConstructedReturnBodies::try_construct(
            &evaluated,
            &[invalid],
            &ExecutionState::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts
        )
        .is_none()
    );
}

#[test]
fn existential_binding_retains_the_recorded_word_origin() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_850_010));
    let hidden = Address::symbolic(Variable(8_850_011));
    let mut definition = existential_definition(1);
    definition
        .parameters
        .push(program_parameter("word", ProgramType::UInt64));
    definition.facts.push(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(variable("word")),
        operator: ComparisonOperator::Equal,
        right: SpecExpression::ProgramExpression(cast(variable("hidden"), ProgramType::UInt64)),
    });
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own_composite(
                "existential_return".into(),
                vec![
                    ProgramValue::pointer(pointer),
                    ProgramValue::UInt64(MachineTerm::pointer_address(hidden.clone())),
                ],
            ),
            ReturnOwnershipOrigin::Description,
            &facts,
        )
        .unwrap();
    let source = evaluated.occurrences[0].source;
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[definition],
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(source).unwrap();
    assert_eq!(
        body.witnesses[&source],
        vec![ProgramValue::pointer(hidden.clone())]
    );
    assert_eq!(body.transfers[1].fact, owner(hidden, 0, 1));
}

#[test]
fn nested_existential_returns_keep_bindings_and_do_not_infer_them_from_siblings() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_850_030));
    let mut outer = existential_definition(0);
    outer
        .witnesses
        .push(program_parameter("second", ProgramType::Int32Pointer));
    outer.contains.push(composite_spec(
        "leaf",
        variable("hidden"),
        ResourceTransferRole::Borrow,
    ));
    outer.contains.push(composite_spec(
        "leaf",
        variable("second"),
        ResourceTransferRole::Borrow,
    ));
    let leaf = CompositeResourceDefinition::new(
        "leaf",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    );
    let evaluated = existential_outputs(pointer, 1, &facts);
    let source = evaluated.occurrences[0].source;
    let _fast =
        crate::kernel::search::FastOperationScope::enter("multiple nested returned witnesses");
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[outer, leaf],
        &ExecutionState::new(),
        &facts,
    );
    assert!(!bodies.0.is_empty());
    let body = bodies.get(source).unwrap();
    let values = &body.witnesses[&source];
    assert_eq!(values.len(), 2);
    assert_ne!(values[0], values[1]);
    let nested = body
        .transfers
        .iter()
        .filter(|transfer| transfer.parent != source)
        .collect::<Vec<_>>();
    assert_eq!(nested.len(), 2);
    for (value, child) in values.iter().zip(nested) {
        let ProgramValue::Pointer(pointer) = value else {
            panic!("pointer witness");
        };
        assert_eq!(child.fact, owner(pointer.pointer().clone(), 0, 1));
        assert!(
            body.transfers
                .iter()
                .any(|parent| parent.source == child.parent)
        );
    }
}

#[test]
fn a_nested_witness_does_not_select_a_matching_sibling_description() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_850_050));
    let parent = CompositeResourceDefinition::new(
        "a_parent",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            ResourceSpec::composite(
                ResourceAccessMode::Own,
                "b_witnessed".into(),
                vec![],
                vec![],
            ),
            composite_spec("leaf", variable("p"), ResourceTransferRole::Borrow),
        ],
        vec![],
    );
    let mut witnessed = CompositeResourceDefinition::new(
        "b_witnessed",
        vec![],
        None,
        false,
        vec![composite_spec(
            "leaf",
            variable("hidden"),
            ResourceTransferRole::Borrow,
        )],
        vec![],
    );
    witnessed
        .witnesses
        .push(program_parameter("hidden", ProgramType::Int32Pointer));
    let leaf = CompositeResourceDefinition::new(
        "leaf",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            variable("p"),
            int32_literal(0),
            int32_literal(1),
        ))],
        vec![],
    );
    let evaluated = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own_composite(
                "a_parent".into(),
                vec![ProgramValue::pointer(pointer.clone())],
            ),
            ReturnOwnershipOrigin::Description,
            &facts,
        )
        .unwrap();
    let _fast = crate::kernel::search::FastOperationScope::enter(
        "nested witness beside a matching sibling",
    );
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[parent, witnessed, leaf],
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(evaluated.occurrences[0].source).unwrap();
    let nested_source = body.transfers[0].source;
    let [ProgramValue::Pointer(hidden)] = body.witnesses[&nested_source].as_slice() else {
        panic!("one nested witness");
    };
    assert_ne!(hidden.pointer(), &pointer);
    assert!(body.expansion.contains(&owner(pointer, 0, 1)));
    assert!(
        body.expansion
            .contains(&owner(hidden.pointer().clone(), 0, 1))
    );
}
