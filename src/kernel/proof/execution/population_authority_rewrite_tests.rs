use super::*;
use crate::kernel::{ProgramType, program_function};

#[test]
fn exact_composition_observation_accepts_retained_views_but_not_foreign_ownership() {
    let (state, _) = source_state();
    let pointer = state.locals.slot("anchor").unwrap().clone();
    let range = MemoryRange::new(pointer, 0.into(), 1.into());
    let context = ResourceContext::new().unchecked_with_facts([
        ResourceFact::own_memory(range.clone()),
        ResourceFact::view_memory(range),
    ]);
    let assumptions = PureFactContext::default();
    assert!(resource_composition_is_supported_by(
        &Proposition::ResourceComposition(context.clone()),
        &context,
        &assumptions,
    ));
    let framed = context
        .clone()
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            SymbolicMemory::local_pointer("framed_scalar"),
            0.into(),
            1.into(),
        )));
    assert!(resource_composition_is_supported_by(
        &Proposition::ResourceComposition(context.clone()),
        &framed,
        &assumptions,
    ));
    let duplicated = context
        .clone()
        .unchecked_with_fact(context.facts()[0].clone());
    assert!(!resource_composition_is_supported_by(
        &Proposition::ResourceComposition(duplicated),
        &framed,
        &assumptions,
    ));
    let foreign =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            Address {
                base: "local:foreign".into(),
                offset: crate::kernel::OldAddressOffset::Constant(0),
            },
            0.into(),
            1.into(),
        )));
    assert!(!resource_composition_is_supported_by(
        &Proposition::ResourceComposition(foreign),
        &context,
        &assumptions,
    ));
}

fn source_state() -> (ExecutionState, ResourceFact) {
    let mut state = ExecutionState::new()
        .with_local("anchor", crate::kernel::int32(0))
        .with_population_creation_tracking();
    let pointer = state.locals.slot("anchor").unwrap().clone();
    state.set_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 4));
    state.record_population_storage_creation(pointer.base.clone());
    let description = crate::kernel::ResourceDescription::new(
        "reference".into(),
        vec![ProgramValue::pointer(pointer).into()].into(),
        crate::kernel::ResourceFieldSchema::new(vec![]).unwrap(),
    );
    (
        state,
        ResourceFact::own(Resource::PopulationAuthority(description)),
    )
}

#[test]
fn checked_authority_events_require_their_exact_predecessor() {
    let (before, selected) = source_state();
    let assumptions = PureFactContext::new();
    let event =
        CheckedPopulationAuthorityRewrite::construct(&before, &selected, true, &assumptions)
            .unwrap();
    let established = event.advance_checked(&before).unwrap();
    assert!(
        established
            .resources()
            .contains_exact_representation(&selected)
    );

    let missing_storage = before.clone().with_memory(SymbolicMemory::new());
    assert!(event.advance_checked(&missing_storage).is_none());
    assert!(
        CheckedPopulationAuthorityRewrite::construct(
            &missing_storage,
            &selected,
            true,
            &assumptions
        )
        .is_err()
    );

    let other_resources = before.clone().with_resource_context(
        before
            .resources()
            .clone()
            .unchecked_with_fact(ResourceFact::own_token("other".into(), vec![])),
    );
    assert!(event.advance_checked(&other_resources).is_none());
    let other_observations = before.clone().with_observed_population_family("reference");
    assert!(event.advance_checked(&other_observations).is_none());

    let retirement =
        CheckedPopulationAuthorityRewrite::construct(established, &selected, false, &assumptions)
            .unwrap();
    let retired = retirement.advance_checked(established).unwrap();
    assert!(!retired.resources().contains_exact_representation(&selected));
    assert!(retirement.advance_checked(&before).is_none());
    assert!(event.advance_checked(retired).is_none());

    // A second checked exchange from the same predecessor issues a distinct
    // creation history, even though its authority has the same spelling.
    let sibling =
        CheckedPopulationAuthorityRewrite::construct(&before, &selected, true, &assumptions)
            .unwrap();
    assert!(
        retirement
            .advance_checked(sibling.advance_checked(&before).unwrap())
            .is_none()
    );
    assert!(
        CheckedPopulationAuthorityRewrite::construct(retired, &selected, true, &assumptions)
            .is_err()
    );
}

#[test]
fn checked_member_events_conserve_one_occurrence_and_reject_forged_deltas() {
    let (before, authority) = source_state();
    let facts = PureFactStore::default();
    let (established, _) = before
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let Resource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = ResourceFact::own(Resource::Composite {
        name: description.family().to_owned(),
        arguments: description.arguments().to_vec().into(),
    });
    let function = program_function(
        ProgramType::Void,
        "value",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "reference",
        vec![],
        None,
        false,
        vec![],
        vec![],
    )]);
    let definition = function
        .proof_composite_resource_definition("reference")
        .unwrap();
    let (one, birth) = established
        .checked_population_member_exchange(&member, true, definition, facts.assumptions())
        .unwrap();
    CheckedPopulationMemberRewrite::check(
        &function,
        &established,
        &facts,
        &member,
        true,
        &birth,
        &one,
        &facts,
    )
    .unwrap();
    assert!(
        established
            .checked_population_member_exchange(&member, false, definition, facts.assumptions())
            .is_err()
    );
    assert!(
        one.checked_population_authority_exchange(&authority, false, facts.assumptions())
            .is_err()
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function,
            &established,
            &facts,
            &member,
            true,
            &birth,
            &one.clone().with_resource_context(ResourceContext::new()),
            &facts,
        )
        .is_err()
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function,
            &established,
            &facts,
            &member,
            true,
            &birth,
            &one.clone().with_memory(SymbolicMemory::new()),
            &facts,
        )
        .is_err()
    );
    let (zero, death) = one
        .checked_population_member_exchange(&member, false, definition, facts.assumptions())
        .unwrap();
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &death, &zero, &facts,
        )
        .is_ok()
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &birth, &zero, &facts,
        )
        .is_err()
    );
    assert!(
        zero.checked_population_member_exchange(&member, false, definition, facts.assumptions())
            .is_err()
    );
}

#[test]
fn member_exchange_requires_both_external_body_ownership_and_checked_span() {
    let (state, authority) = source_state();
    let external = crate::kernel::Address {
        base: crate::kernel::AddressBase::ExternalArgument,
        offset: crate::kernel::OldAddressOffset::Constant(16),
    };
    let Resource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = ResourceFact::own(Resource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let definition = CompositeResourceDefinition::new(
        "reference",
        vec![crate::kernel::program_parameter(
            "p",
            ProgramType::Int32Pointer,
        )],
        None,
        false,
        vec![ResourceSpec::owned_memory(
            crate::kernel::MemorySegment::new(
                ProgramExpression::Value(ProgramValue::pointer(external.clone())),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            ),
        )],
        vec![],
    );
    let function = program_function(ProgramType::Void, "member", vec![], ProgramStatement::Skip)
        .with_composite_resource_definitions(vec![definition.clone()]);
    let (empty, _) = state
        .checked_population_authority_exchange(&authority, true, &PureFactContext::new())
        .unwrap();
    let owned = empty
        .clone()
        .with_resource_context(empty.resources().clone().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(external.clone(), 0.into(), 1.into())),
        ));
    assert!(
        owned
            .checked_population_member_exchange(&member, true, &definition, &PureFactContext::new())
            .is_err()
    );
    let span = |bytes| Proposition::MemoryLoadable {
        memory: owned.memory().clone(),
        base: external.clone(),
        bytes: (OldMachineTerm::constant(bytes)).into(),
        wide: false,
    };
    let small = PureFactStore::default().with_fact(span(1));
    assert!(
        owned
            .checked_population_member_exchange(&member, true, &definition, small.assumptions())
            .is_err()
    );
    let facts = PureFactStore::default().with_fact(span(4));
    assert!(
        empty
            .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
            .is_err()
    );
    let (one, witness) = owned
        .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
        .unwrap();
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function, &owned, &facts, &member, true, &witness, &one, &facts
        )
        .is_ok()
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function, &owned, &small, &member, true, &witness, &one, &small
        )
        .is_err()
    );
    // The checked introduction packaged the span evidence in the owned
    // member. Its elimination needs custody, not the original ambient fact.
    let no_facts = PureFactContext::new();
    let (returned, _) = one
        .checked_population_member_exchange(&member, false, &definition, &no_facts)
        .expect("owned membership carries its checked private body");
    assert!(returned.resources().satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new(external.clone(), 0.into(), 1.into())),
        &no_facts,
    ));
    for absent in [&empty, &returned] {
        assert!(
            absent
                .checked_population_member_exchange(&member, false, &definition, &no_facts)
                .is_err()
        );
    }
}

#[test]
fn checked_member_exchange_transfers_exact_contained_resource() {
    for abstract_token in [false, true] {
        let (state, authority) = source_state();
        let facts = PureFactStore::default();
        let Resource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = ResourceFact::own(Resource::Composite {
            name: "reference".into(),
            arguments: description.arguments().to_vec().into(),
        });
        let (child, child_spec) = if abstract_token {
            (
                ResourceFact::own(Resource::Token {
                    name: "payload".into(),
                    arguments: vec![crate::kernel::int32(7).into()].into(),
                }),
                ResourceSpec::token(
                    crate::kernel::ResourceAccessMode::Own,
                    "payload".into(),
                    vec![crate::kernel::program_expression::int32_literal(7)],
                    vec![ProgramType::Int32],
                ),
            )
        } else {
            (
                ResourceFact::own(Resource::Composite {
                    name: "payload".into(),
                    arguments: description.arguments().to_vec().into(),
                }),
                ResourceSpec::composite(
                    crate::kernel::ResourceAccessMode::Own,
                    "payload".into(),
                    vec![crate::kernel::program_expression::variable("p")],
                    vec![ProgramType::Int32Pointer],
                ),
            )
        };
        let definition = CompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::program_parameter(
                "p",
                ProgramType::Int32Pointer,
            )],
            None,
            false,
            vec![child_spec],
            vec![],
        );
        let function = program_function(
            ProgramType::Void,
            "member",
            vec![],
            ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let (empty, _) = state
            .checked_population_authority_exchange(&authority, true, facts.assumptions())
            .unwrap();
        assert!(
                empty
                    .checked_population_member_exchange(
                        &member,
                        true,
                        &definition,
                        facts.assumptions(),
                    )
                    .is_err()
            );
        let empty = empty
            .clone()
            .with_resource_context(empty.resources().clone().unchecked_with_fact(child.clone()));
        let (one, birth) = empty
            .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
            .unwrap();
        assert!(!one.resources().satisfies_fact(&child, facts.assumptions()));
        assert!(one.resources().satisfies_fact(&member, facts.assumptions()));
        CheckedPopulationMemberRewrite::check(
            &function, &empty, &facts, &member, true, &birth, &one, &facts,
        )
        .unwrap();
        let duplicated = one
            .clone()
            .with_resource_context(one.resources().clone().unchecked_with_fact(child.clone()));
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &empty,
                &facts,
                &member,
                true,
                &birth,
                &duplicated,
                &facts,
            )
            .is_err()
        );
        assert!(
                one.checked_population_member_exchange(
                    &member,
                    true,
                    &definition,
                    facts.assumptions(),
                )
                .is_err()
            );
        let (zero, death) = one
            .checked_population_member_exchange(&member, false, &definition, facts.assumptions())
            .unwrap();
        assert!(zero.resources().satisfies_fact(&child, facts.assumptions()));
        assert!(
            !zero
                .resources()
                .satisfies_fact(&member, facts.assumptions())
        );
        CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &death, &zero, &facts,
        )
        .unwrap();
        let missing = zero.clone().with_resource_context(
            zero.resources()
                .clone()
                .without_fact_incrementally(&child, facts.assumptions())
                .unwrap(),
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &one, &facts, &member, false, &death, &missing, &facts,
            )
            .is_err()
        );
    }
}

#[test]
fn member_body_facts_require_checked_birth_and_reject_forged_consumption_facts() {
    let (state, authority) = source_state();
    let facts = PureFactStore::default();
    let (state, _) = state
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let Resource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = ResourceFact::own(Resource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let definition = |right| {
        CompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::program_parameter(
                "p",
                ProgramType::Int32Pointer,
            )],
            None,
            false,
            vec![],
            vec![crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::Value(crate::kernel::int32(1)),
                operator: crate::kernel::ComparisonOperator::Equal,
                right: crate::kernel::SpecExpression::Value(crate::kernel::int32(right)),
            }],
        )
    };
    assert!(
        state
            .checked_population_member_exchange(&member, true, &definition(2), facts.assumptions())
            .is_err()
    );
    let definition = definition(1);
    let function = program_function(
        ProgramType::Void,
        "member",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let (one, birth) = state
        .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
        .unwrap();
    CheckedPopulationMemberRewrite::check(
        &function, &state, &facts, &member, true, &birth, &one, &facts,
    )
    .unwrap();
    let (zero, death) = one
        .checked_population_member_exchange(&member, false, &definition, facts.assumptions())
        .unwrap();
    let body_facts = crate::kernel::functions::instantiate_composite_resource_facts(
        &member,
        std::slice::from_ref(&definition),
        one.memory(),
        zero.resources(),
        facts.assumptions(),
    )
    .unwrap();
    let mut exposed = facts.clone();
    for fact in body_facts.propositions {
        exposed = exposed.with_fact(fact);
    }
    CheckedPopulationMemberRewrite::check(
        &function, &one, &facts, &member, false, &death, &zero, &exposed,
    )
    .unwrap();
    let forged_facts = exposed.with_fact(Proposition::condition_is(
        crate::kernel::OldConditionTerm::Constant(false),
        true,
    ));
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function,
            &one,
            &facts,
            &member,
            false,
            &death,
            &zero,
            &forged_facts
        )
        .is_err()
    );
}

#[test]
fn consuming_private_member_publishes_definedness_at_the_current_point() {
    use crate::kernel::{MemorySegment, SpecExpression, SpecPoint, SpecProposition};
    use crate::kernel::{int32, program_expression, program_parameter};

    let _session = crate::kernel::VerificationSession::enter();
    let (before, authority) = source_state();
    let Resource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = ResourceFact::own(Resource::Composite {
        name: description.family().to_owned(),
        arguments: description.arguments().to_vec().into(),
    });
    let pointer = before.locals.slot("anchor").unwrap().clone();
    let memory = before.memory().clone().store(pointer.clone(), int32(7));
    let owned = ResourceFact::own_memory(MemoryRange::new(pointer.clone(), 0.into(), 1.into()));
    let before = before
        .with_memory(memory)
        .with_resource_context(ResourceContext::new().unchecked_with_fact(owned));
    let facts = PureFactStore::default();
    let (before, _) = before
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let definition = CompositeResourceDefinition::new(
        "reference",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            program_expression::variable("p"),
            program_expression::int32_literal(0),
            program_expression::int32_literal(1),
        ))],
        vec![SpecProposition::Defined(SpecExpression::MemoryLoad {
            point: SpecPoint::Current,
            pointer: Box::new(SpecExpression::ProgramExpression(
                program_expression::variable("p"),
            )),
            value_type: ProgramType::Int32,
            exact: false,
        })],
    )
    .with_authorized(true);
    let function = program_function(
        ProgramType::Void,
        "member",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let defined_at = |state: &ExecutionState| Proposition::MemoryReadDefined {
        at: Some(state.observation_point_id().unwrap()),
        memory: state.memory().clone(),
        pointer: pointer.clone(),
        value_type: ProgramType::Int32,
    };
    let birth_facts = facts.clone().with_fact(defined_at(&before));
    let (member_state, _) = before
        .checked_population_member_exchange(&member, true, &definition, birth_facts.assumptions())
        .unwrap();
    let consuming = member_state
        .clone()
        .with_memory(member_state.memory().clone());
    assert_ne!(
        consuming.observation_point_id(),
        before.observation_point_id()
    );
    assert!(consuming.memory().same_storage_roots(before.memory()));
    let (after, death) = consuming
        .checked_population_member_exchange(&member, false, &definition, facts.assumptions())
        .unwrap();
    let body_facts = crate::kernel::functions::instantiate_private_member_body_facts(
        &member,
        &definition,
        &consuming,
        facts.assumptions(),
    )
    .unwrap();
    assert_eq!(body_facts.declared, vec![(0, defined_at(&consuming))]);
    let exposed = body_facts
        .propositions
        .into_iter()
        .fold(facts.clone(), |facts, fact| facts.with_fact(fact));
    CheckedPopulationMemberRewrite::check(
        &function, &consuming, &facts, &member, false, &death, &after, &exposed,
    )
    .unwrap();
}

#[test]
fn checked_member_events_exchange_private_memory_and_reject_duplicate_birth() {
    use crate::kernel::{MemorySegment, program_parameter};

    let (before, authority) = source_state();
    let Resource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = ResourceFact::own(Resource::Composite {
        name: description.family().to_owned(),
        arguments: description.arguments().to_vec().into(),
    });
    let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
        (description.arguments()).fixed_values::<1>()
    else {
        unreachable!()
    };
    let memory = ResourceFact::own_memory(MemoryRange::new(
        pointer.address().clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    let definition = CompositeResourceDefinition::new(
        "reference",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )
    .with_authorized(true);
    let function = program_function(
        ProgramType::Void,
        "value",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition]);
    let definition = function
        .proof_composite_resource_definition("reference")
        .unwrap();
    let facts = PureFactStore::default();
    let (established, _) = before
        .with_resource_context(ResourceContext::new().unchecked_with_fact(memory.clone()))
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let (one, birth) = established
        .checked_population_member_exchange(&member, true, definition, facts.assumptions())
        .unwrap();
    assert!(!one.resources().satisfies_fact(&memory, facts.assumptions()));
    assert!(one.resources().satisfies_fact(&member, facts.assumptions()));
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function,
            &established,
            &facts,
            &member,
            true,
            &birth,
            &one,
            &facts,
        )
        .is_ok()
    );
    assert!(
        one.checked_population_member_exchange(&member, true, definition, facts.assumptions())
            .is_err()
    );
    let Resource::Composite { name, arguments } = member.resource() else {
        unreachable!()
    };
    let expanded = crate::kernel::functions::expand_composite_resource_fact(
        &ResourceContext::new().unchecked_with_fact(member.clone()),
        &member,
        std::slice::from_ref(definition),
        &one.program_point(),
        facts.assumptions(),
    )
    .unwrap();
    let opened = one
        .clone()
        .with_resource_context(
            one.resources()
                .clone()
                .try_compose_with_facts_delaying_normalization(
                    expanded.facts().iter().cloned(),
                    facts.assumptions(),
                )
                .unwrap(),
        )
        .open_population_body(name.clone(), arguments.clone())
        .unwrap();
    CheckedResourceRewrite::check(
        &function,
        &one,
        &facts,
        &member,
        &opened,
        &facts,
        &CheckedCallEvents::default(),
    )
    .unwrap();
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &one,
            &facts,
            &member,
            &opened.clone().with_memory(SymbolicMemory::new()),
            &facts,
            &CheckedCallEvents::default(),
        )
        .is_err()
    );
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &one,
            &facts,
            &member,
            &opened
                .clone()
                .with_resource_context(established.resources().clone()),
            &facts,
            &CheckedCallEvents::default(),
        )
        .is_err()
    );
    let closed = opened
        .clone()
        .with_resource_context(
            opened
                .resources()
                .clone()
                .without_fact_incrementally(&expanded.facts()[0], facts.assumptions())
                .unwrap(),
        )
        .close_population_body(name.clone(), arguments.clone())
        .unwrap();
    CheckedResourceRewrite::check(
        &function,
        &opened,
        &facts,
        &member,
        &closed,
        &facts,
        &CheckedCallEvents::default(),
    )
    .unwrap();
    assert_eq!(closed, one);
    let (zero, death) = one
        .checked_population_member_exchange(&member, false, definition, facts.assumptions())
        .unwrap();
    assert!(
        zero.resources()
            .satisfies_fact(&memory, facts.assumptions())
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &death, &zero, &facts,
        )
        .is_ok()
    );
    assert!(
        CheckedPopulationMemberRewrite::check(
            &function,
            &established,
            &facts,
            &member,
            true,
            &birth,
            &one.clone()
                .with_resource_context(established.resources().clone()),
            &facts,
        )
        .is_err()
    );
}

#[test]
fn generic_resource_observations_cannot_check_under_authority_history() {
    let (before, _) = source_state();
    let selected = ResourceFact::own_composite("reference".into(), Vec::new());
    let facts = PureFactStore::default();
    let function = program_function(
        ProgramType::Void,
        "value",
        vec![],
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "reference",
        vec![],
        None,
        false,
        vec![],
        vec![],
    )]);
    assert!(
        CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &before,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .is_err()
    );
}

#[test]
fn authority_history_refuses_wildcard_count_evaluation() {
    let (state, _) = source_state();
    let count = crate::kernel::SpecExpression::CountedResourceCount {
        name: "reference".into(),
        arguments: vec![None],
    };
    assert_eq!(
        crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
            &state,
            &count,
            &PureFactContext::new(),
            &std::collections::BTreeMap::new(),
            &mut crate::kernel::ExecutionBudget::beside_live_state(),
        )
        .err(),
        Some(crate::kernel::ExecutionLimit::AuthorityCountNeedsExactPointer),
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/population_authority_rewrite_tests.rs");
}
