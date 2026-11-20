use super::*;
use crate::kernel::program_expression::{add, int32_literal, subtract, variable};

pub(super) fn recursive_definition() -> CompositeResourceDefinition {
    let child = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::Own,
        "finite_list".into(),
        vec![
            add(variable("p"), int32_literal(1)),
            subtract(variable("remaining"), int32_literal(1)),
        ],
        vec![ProgramType::Int32Pointer, ProgramType::Int32],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    let mut definition = CompositeResourceDefinition::new(
        "finite_list",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("remaining", ProgramType::Int32),
        ],
        None,
        true,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                variable("p"),
                int32_literal(0),
                int32_literal(1),
            )),
            child,
        ],
        vec![],
    );
    definition.condition = Some(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(variable("remaining")),
        operator: ComparisonOperator::NotEqual,
        right: SpecExpression::ProgramExpression(int32_literal(0)),
    });
    definition
}

pub(super) fn recursive_output(
    pointer: Address,
    remaining: MachineTerm,
    facts: &PureFactContext,
) -> EvaluatedReturnResources {
    EvaluatedReturnResources::new(facts)
        .admit(
            ResourceFact::own_composite(
                "finite_list".into(),
                vec![
                    ProgramValue::pointer(pointer),
                    ProgramValue::Int32(remaining),
                ],
            ),
            ReturnOwnershipOrigin::Description,
            facts,
        )
        .unwrap()
}

#[test]
fn recursive_return_retains_one_explicit_frontier_and_its_actual_child_identity() {
    let facts = PureFactContext::new();
    let pointer = Address::symbolic(Variable(8_860_000));
    let evaluated = recursive_output(pointer, MachineTerm::constant(64), &facts);
    let source = evaluated.occurrences[0].source;
    let state = ExecutionState::new();
    let bodies =
        ConstructedReturnBodies::construct(&evaluated, &[recursive_definition()], &state, &facts);
    assert!(!bodies.0.is_empty());
    let body = bodies.get(source).unwrap();
    assert_eq!(body.transfers.len(), 2);
    assert_eq!(body.expansion.len(), 2);
    assert_eq!(
        body.folded,
        vec![(body.transfers[1].fact.clone(), body.transfers[1].source)]
    );
    assert_eq!(body.transfers[1].parent, source);
    assert!(matches!(
        body.folded[0].0.resource(),
        Resource::Composite { .. }
    ));
    let (destination, transfers) = evaluated
        .restore_entry_borrows(
            ResourceContext::new(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap()
        .finish(&facts)
        .unwrap();
    // No definitions: projection must consume the carried finite frontier.
    let projections = project_return_resource_cores(
        &evaluated.resources,
        &transfers,
        &bodies,
        &facts,
        &destination,
    );
    assert_eq!(projections[0].expansion, body.expansion);
    assert_eq!(projections[0].viewed_children, body.viewed_children);
}

#[test]
fn recursive_empty_and_undecided_guards_retain_the_correct_finite_boundary() {
    let facts = PureFactContext::new();
    for (remaining, opaque) in [
        (MachineTerm::constant(0), false),
        (MachineTerm::Variable(Variable(8_860_001)), true),
    ] {
        let evaluated = recursive_output(Address::symbolic(Variable(8_860_002)), remaining, &facts);
        let source = evaluated.occurrences[0].source;
        let bodies = ConstructedReturnBodies::construct(
            &evaluated,
            &[recursive_definition()],
            &ExecutionState::new(),
            &facts,
        );
        let body = bodies.get(source).unwrap();
        assert!(body.boundary.is_empty());
        assert!(body.frontier.is_empty());
        assert_eq!(body.folded.len(), usize::from(opaque));
        assert_eq!(body.expansion.len(), usize::from(opaque));
        if opaque {
            assert_eq!(body.folded[0].1, source);
            assert_eq!(
                body.folded[0].0,
                *evaluated
                    .resources
                    .owned_fact_for_occurrence(source)
                    .unwrap()
            );
        }
    }
}

#[test]
fn recursive_visible_memory_still_refuses_a_held_alias_and_preserves_branches() {
    let pointer = Address::symbolic(Variable(8_860_003));
    let alias = Address::symbolic(Variable(8_860_004));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::address_equal(pointer.clone(), alias.clone()),
        true,
    );
    let evaluated = recursive_output(pointer, MachineTerm::constant(64), &facts);
    let source = evaluated.occurrences[0].source;
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[recursive_definition()],
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(source).unwrap();
    let parent = ResourceContext::new_with_equalities(&facts);
    let held = ResourceFact::own_memory(MemoryRange::new(alias, 0u32.into(), 1u32.into()));
    let branch = parent.clone().unchecked_with_fact(held.clone());
    branch.synchronize_memory_equalities(&facts);
    let check = |frame: &ResourceContext| {
        produced_composite_frontier_conflict(
            frame,
            std::iter::once((
                evaluated
                    .resources
                    .owned_fact_for_occurrence(source)
                    .unwrap(),
                Some(body),
            )),
            &facts,
        )
    };
    assert!(check(&parent).is_none());
    let Some(RuntimeError::ProducedCompositeOverlapsHeldResource { held: selected, .. }) =
        check(&branch)
    else {
        panic!("visible memory must conflict");
    };
    assert_eq!(*selected, held);
    assert!(check(&parent).is_none());
}

#[test]
fn viewed_recursive_children_remain_folded_views_with_emitted_identities() {
    let facts = PureFactContext::new();
    let mut definition = recursive_definition();
    let ResourceTerm::Composite {
        name,
        arguments,
        parameter_types,
        ..
    } = definition.contains[1].term().clone()
    else {
        unreachable!()
    };
    definition.contains[1] = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        name,
        arguments,
        parameter_types,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    let evaluated = recursive_output(
        Address::symbolic(Variable(8_860_005)),
        MachineTerm::constant(3),
        &facts,
    );
    let source = evaluated.occurrences[0].source;
    let bodies = ConstructedReturnBodies::construct(
        &evaluated,
        &[definition],
        &ExecutionState::new(),
        &facts,
    );
    let body = bodies.get(source).unwrap();
    assert!(body.folded[0].0.is_view());
    assert_eq!(body.viewed_children, body.folded);
    assert_eq!(body.transfers[1].origin, ReturnOwnershipOrigin::Description);
}
