// Scaling tests of `src/kernel/proof/execution.rs` (module `population_authority_rewrite_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn private_member_facts_cannot_use_ambient_cell_ownership() {
    use crate::kernel::{CMemorySegment, c_int32_literal, c_parameter, c_variable};
    let (_, authority) = source_state();
    let CResource::PopulationAuthority(description) = authority.resource() else {
        unreachable!()
    };
    let member = CResourceFact::own(CResource::Composite {
        name: "reference".into(),
        arguments: description.arguments().to_vec().into(),
    });
    let [crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments()
    else {
        unreachable!()
    };
    let pointer = pointer.pointer();
    let memory = CMemory::new().with_block(pointer.block.clone(), 8).store(
        pointer.offset_by_elements(1.into(), 4),
        crate::kernel::int32(0),
    );
    let resources = ResourceContext::new().unchecked_with_facts([
        CResourceFact::own_memory(CMemoryRange::new(pointer.clone(), 0.into(), 1.into())),
        CResourceFact::own_memory(CMemoryRange::new(pointer.clone(), 1.into(), 2.into())),
    ]);
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
        vec![crate::kernel::SpecProposition::Comparison {
            left: crate::kernel::SpecExpression::CExpression(crate::kernel::c_index(
                c_variable("p"),
                c_int32_literal(1),
            )),
            operator: crate::kernel::CComparisonOperator::Equal,
            right: crate::kernel::SpecExpression::Value(crate::kernel::int32(0)),
        }],
    );
    let assumptions = PureFactContext::default();
    assert!(
        crate::kernel::functions::instantiate_composite_resource_facts(
            &member,
            std::slice::from_ref(&definition),
            &memory,
            &resources,
            &assumptions,
        )
        .is_some()
    );
    assert!(
        crate::kernel::functions::instantiate_private_member_body_facts(
            &member,
            &definition,
            &CState::new()
                .with_population_creation_tracking()
                .with_memory(memory.clone())
                .with_resource_context(resources.clone()),
            &assumptions,
        )
        .is_none()
    );
    let work = [8, 32, 128, 512].map(|locals| {
        let mut state = CState::new()
            .with_population_creation_tracking()
            .with_memory(memory.clone())
            .with_resource_context(resources.clone());
        for index in 0..locals {
            state = state.with_local(format!("unrelated_{index}"), crate::kernel::int32(index));
        }
        let (instantiated, work) = crate::persistent::measure_persistent_work(|| {
            crate::kernel::functions::instantiate_private_member_body_facts(
                &member,
                &definition,
                &state,
                &assumptions,
            )
        });
        assert!(instantiated.is_none());
        work
    });
    assert!(
        work[0] > 0,
        "member fact checking must charge work: {work:?}"
    );
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 128),
        "member fact checking must not visit unrelated caller locals: {work:?}"
    );
}

#[test]
fn authority_count_observation_rejects_unchecked_deltas_and_scales() {
    let work = [16usize, 64, 256].map(|size| {
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
        let definition = CCompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )
        .with_authorized(true);
        let (mut state, _) = state
            .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
            .unwrap();
        let mut resources = state.resources().clone();
        for index in 0..size {
            state = state.with_local(
                format!("unrelated_{index}"),
                crate::kernel::int32(index as u32),
            );
            resources = resources.unchecked_with_fact(CResourceFact::own_token(
                format!("unrelated_{index}"),
                vec![],
            ));
        }
        state = state.with_resource_context(resources);
        let function = c_function(
            CType::Void,
            "observe",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let bound = crate::kernel::api::checked_owned_resource_count_lower_bound(
            &state,
            &member,
            facts.assumptions(),
        )
        .unwrap();
        let after_facts = facts.with_fact(bound);
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            let observation = CheckedResourceObservation::check(
                &function,
                &state,
                &facts,
                &member,
                &state,
                &after_facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .unwrap();
            assert!(observation.definition().is_none());
        });
        let forged_facts = after_facts.with_fact(Proposition::Predicate {
            name: "unproved_body_fact".into(),
            arguments: vec![],
        });
        assert!(
            CheckedResourceObservation::check(
                &function,
                &state,
                &facts,
                &member,
                &state,
                &forged_facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
        let added_member = state.clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_fact(CResourceFact::own_token("forged_child".into(), vec![])),
        );
        assert!(
            CheckedResourceObservation::check(
                &function,
                &state,
                &facts,
                &member,
                &added_member,
                &after_facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
        for missing in [&member, &authority] {
            let missing = state.clone().with_resource_context(
                state
                    .resources()
                    .clone()
                    .without_fact_incrementally(missing, facts.assumptions())
                    .unwrap(),
            );
            assert!(
                CheckedResourceObservation::check(
                    &function,
                    &missing,
                    &facts,
                    &member,
                    &missing,
                    &after_facts,
                    &PersistentOrderedSet::default(),
                    &CheckedCallEvents::default(),
                )
                .is_err()
            );
        }
        work
    });
    assert!(
        work[0] > 0,
        "count observation must charge checked work: {work:?}"
    );
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 64),
        "count observation scanned unrelated state: {work:?}"
    );
}
