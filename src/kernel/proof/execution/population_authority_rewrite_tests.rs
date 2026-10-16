use super::*;
use crate::kernel::{CType, c_function};

#[test]
fn exact_composition_observation_accepts_retained_views_but_not_foreign_ownership() {
    let (state, _) = source_state();
    let pointer = state.locals.slot("anchor").unwrap().clone();
    let range = CMemoryRange::new(pointer, 0.into(), 1.into());
    let context = ResourceContext::new().unchecked_with_facts([
        CResourceFact::own_memory(range.clone()),
        CResourceFact::view_memory(range),
    ]);
    let assumptions = PureFactContext::default();
    assert!(resource_composition_is_supported_by(
        &Proposition::CResourceComposition(context.clone()),
        &context,
        &assumptions,
    ));
    let framed = context
        .clone()
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            CMemory::local_pointer("framed_scalar"),
            0.into(),
            1.into(),
        )));
    assert!(resource_composition_is_supported_by(
        &Proposition::CResourceComposition(context.clone()),
        &framed,
        &assumptions,
    ));
    let duplicated = context
        .clone()
        .unchecked_with_fact(context.facts()[0].clone());
    assert!(!resource_composition_is_supported_by(
        &Proposition::CResourceComposition(duplicated),
        &framed,
        &assumptions,
    ));
    let foreign =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            Pointer {
                block: "local:foreign".into(),
                offset: crate::kernel::PointerOffsetTerm::Constant(0),
            },
            0.into(),
            1.into(),
        )));
    assert!(!resource_composition_is_supported_by(
        &Proposition::CResourceComposition(foreign),
        &context,
        &assumptions,
    ));
}

fn source_state() -> (CState, CResourceFact) {
    let mut state = CState::new()
        .with_local("anchor", crate::kernel::int32(0))
        .with_population_creation_tracking();
    let pointer = state.locals.slot("anchor").unwrap().clone();
    state.set_memory(CMemory::new().with_block(pointer.block.clone(), 4));
    state.record_population_storage_creation(pointer.block.clone());
    let description = crate::kernel::ResourceDescription::new(
        "reference".into(),
        vec![CValue::pointer(pointer).into()].into(),
        crate::kernel::ResourceFieldSchema::new(vec![]).unwrap(),
    );
    (
        state,
        CResourceFact::own(CResource::PopulationAuthority(description)),
    )
}

#[test]
fn checked_authority_events_reject_forged_deltas() {
    let (before, selected) = source_state();
    let facts = ProofFacts::default();
    let (established, witness) = before
        .checked_population_authority_exchange(&selected, true, facts.assumptions())
        .unwrap();
    let event = CheckedPopulationAuthorityRewrite::check(
        &before,
        &facts,
        &selected,
        true,
        &witness,
        &established,
        &facts,
    )
    .unwrap();
    assert!(event.advance_checked(&before, &facts).is_some());
    let forged_memory = established
        .clone()
        .with_memory(CMemory::new().with_block("local:forged", 4));
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &before,
            &facts,
            &selected,
            true,
            &witness,
            &forged_memory,
            &facts,
        )
        .is_err()
    );
    let mut forged_event = event.clone();
    forged_event.after_state = forged_memory;
    assert!(forged_event.advance_checked(&before, &facts).is_none());
    let missing_storage_before = before.clone().with_memory(CMemory::new());
    let missing_storage_after = established.clone().with_memory(CMemory::new());
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &missing_storage_before,
            &facts,
            &selected,
            true,
            &witness,
            &missing_storage_after,
            &facts,
        )
        .is_err()
    );
    let forged_resources = established
        .clone()
        .with_resource_context(ResourceContext::new());
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &before,
            &facts,
            &selected,
            true,
            &witness,
            &forged_resources,
            &facts,
        )
        .is_err()
    );
    let forged_observation = established
        .clone()
        .with_observed_population_family("reference");
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &before,
            &facts,
            &selected,
            true,
            &witness,
            &forged_observation,
            &facts,
        )
        .is_err()
    );
    let forged_facts = facts.clone().with_fact(Proposition::ConditionIs(
        crate::kernel::ConditionTerm::Constant(true),
        true,
    ));
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &before,
            &facts,
            &selected,
            true,
            &witness,
            &established,
            &forged_facts,
        )
        .is_err()
    );
    let (retired, retire_witness) = established
        .checked_population_authority_exchange(&selected, false, facts.assumptions())
        .unwrap();
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &established,
            &facts,
            &selected,
            false,
            &retire_witness,
            &retired,
            &facts,
        )
        .is_ok()
    );
    assert!(
        CheckedPopulationAuthorityRewrite::check(
            &established,
            &facts,
            &selected,
            false,
            &witness,
            &retired,
            &facts,
        )
        .is_err()
    );
    assert!(
        before
            .checked_population_authority_exchange(&selected, true, facts.assumptions())
            .is_ok()
    );
    assert!(
        retired
            .checked_population_authority_exchange(&selected, true, facts.assumptions())
            .is_err()
    );
}

#[test]
fn checked_member_events_conserve_one_occurrence_and_reject_forged_deltas() {
    let (before, authority) = source_state();
    let facts = ProofFacts::default();
    let (established, _) = before
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let CResource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = CResourceFact::own(CResource::Composite {
        name: description.family().to_owned(),
        arguments: description.arguments().to_vec().into(),
    });
    let function = c_function(
        CType::Void,
        "value",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
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
    let event = CheckedPopulationMemberRewrite::check(
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
    assert!(event.advance_checked(&established, &facts).is_some());
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
            &one.clone().with_memory(CMemory::new()),
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
fn member_exchange_requires_both_external_body_ownership_and_checked_extent() {
    let (state, authority) = source_state();
    let external = crate::kernel::Pointer {
        block: crate::kernel::PointerBlock::ExternalArgument,
        offset: crate::kernel::PointerOffsetTerm::Constant(16),
    };
    let CResource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let definition = CCompositeResourceDefinition::new(
        "reference",
        vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(
            crate::kernel::CMemorySegment::new(
                CExpression::Value(CValue::pointer(external.clone())),
                crate::kernel::c_int32_literal(0),
                crate::kernel::c_int32_literal(1),
            ),
        )],
        vec![],
    );
    let function = c_function(CType::Void, "member", vec![], CStatement::Skip)
        .with_composite_resource_definitions(vec![definition.clone()]);
    let (empty, _) = state
        .checked_population_authority_exchange(&authority, true, &PureFactContext::new())
        .unwrap();
    let owned = empty
        .clone()
        .with_resource_context(empty.resources().clone().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new(external.clone(), 0.into(), 1.into())),
        ));
    assert!(
        owned
            .checked_population_member_exchange(&member, true, &definition, &PureFactContext::new())
            .is_err()
    );
    let extent = |bytes| Proposition::CMemoryLoadable {
        memory: owned.memory().clone(),
        base: external.clone(),
        bytes: Bitvector32Term::Constant(bytes),
        wide: false,
    };
    let small = ProofFacts::default().with_fact(extent(1));
    assert!(
        owned
            .checked_population_member_exchange(&member, true, &definition, small.assumptions())
            .is_err()
    );
    let facts = ProofFacts::default().with_fact(extent(4));
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
}

#[test]
fn checked_member_exchange_transfers_exact_contained_resource() {
    for abstract_token in [false, true] {
        let (state, authority) = source_state();
        let facts = ProofFacts::default();
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: "reference".into(),
            arguments: description.arguments().to_vec().into(),
        });
        let (child, child_spec) = if abstract_token {
            (
                CResourceFact::own(CResource::Token {
                    name: "payload".into(),
                    arguments: vec![crate::kernel::int32(7).into()].into(),
                }),
                CResourceSpec::token(
                    crate::kernel::CResourceAccessMode::Own,
                    "payload".into(),
                    vec![crate::kernel::c_int32_literal(7)],
                    vec![CType::Int32],
                ),
            )
        } else {
            (
                CResourceFact::own(CResource::Composite {
                    name: "payload".into(),
                    arguments: description.arguments().to_vec().into(),
                }),
                CResourceSpec::composite(
                    crate::kernel::CResourceAccessMode::Own,
                    "payload".into(),
                    vec![crate::kernel::c_variable("p")],
                    vec![CType::Int32Pointer],
                ),
            )
        };
        let definition = CCompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![child_spec],
            vec![],
        );
        let function = c_function(
            CType::Void,
            "member",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
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
        let event = CheckedPopulationMemberRewrite::check(
            &function, &empty, &facts, &member, true, &birth, &one, &facts,
        )
        .unwrap();
        assert!(event.advance_checked(&empty, &facts).is_some());
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
        let event = CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &death, &zero, &facts,
        )
        .unwrap();
        assert!(event.advance_checked(&one, &facts).is_some());
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
    let facts = ProofFacts::default();
    let (state, _) = state
        .checked_population_authority_exchange(&authority, true, facts.assumptions())
        .unwrap();
    let CResource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let definition = |right| {
        CCompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::Value(crate::kernel::int32(1)),
                operator: crate::kernel::CComparisonOperator::Equal,
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
    let function = c_function(
        CType::Void,
        "member",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
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
    let event = CheckedPopulationMemberRewrite::check(
        &function, &one, &facts, &member, false, &death, &zero, &exposed,
    )
    .unwrap();
    assert!(event.advance_checked(&one, &facts).is_some());
    let forged_facts = exposed.with_fact(Proposition::ConditionIs(
        crate::kernel::ConditionTerm::Constant(false),
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
    let mut forged = event;
    forged.after_facts = forged_facts;
    assert!(forged.advance_checked(&one, &facts).is_none());
}

#[test]
fn checked_member_events_exchange_private_memory_and_reject_duplicate_birth() {
    use crate::kernel::{CMemorySegment, c_int32_literal, c_parameter, c_variable};

    let (before, authority) = source_state();
    let CResource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = CResourceFact::own(CResource::Composite {
        name: description.family().to_owned(),
        arguments: description.arguments().to_vec().into(),
    });
    let [crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments()
    else {
        unreachable!()
    };
    let memory = CResourceFact::own_memory(CMemoryRange::new(
        pointer.pointer().clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let definition = CCompositeResourceDefinition::new(
        "reference",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        vec![],
    )
    .with_authorized(true);
    let function = c_function(
        CType::Void,
        "value",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![definition]);
    let definition = function
        .proof_composite_resource_definition("reference")
        .unwrap();
    let facts = ProofFacts::default();
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
    let CResource::Composite { name, arguments } = member.resource() else {
        unreachable!()
    };
    let expanded = crate::kernel::functions::expand_composite_resource_fact(
        &ResourceContext::new().unchecked_with_fact(member.clone()),
        &member,
        std::slice::from_ref(definition),
        one.memory(),
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
            &opened.clone().with_memory(CMemory::new()),
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
    let selected = CResourceFact::own_composite("reference".into(), Vec::new());
    let facts = ProofFacts::default();
    let function = c_function(
        CType::Void,
        "value",
        vec![],
        CStatement::Return(CExpression::Value(CValue::Void)),
    )
    .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
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
