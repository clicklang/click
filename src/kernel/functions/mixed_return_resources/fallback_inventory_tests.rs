//! Migrated output-partition and caller-boundary regression controls.
use super::*;

fn partition() -> (
    PureFactContext,
    Address,
    MachineTerm,
    ResourceFact,
    ResourceFact,
) {
    let p = Address::symbolic(Variable(8_915_000));
    let n = MachineTerm::Variable(Variable(8_915_001));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(1u32.into(), n.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(n.clone(), 8u32.into()),
            true,
        );
    let range = |start, end| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            p.clone(),
            start,
            end,
            1,
        ))
    };
    (
        facts,
        p.clone(),
        n.clone(),
        range(0u32.into(), n.clone()),
        range(n, 16u32.into()),
    )
}

#[test]
fn output_partition_is_constructed_once_and_carried_to_the_caller() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, _, _, left, right) = partition();
    let _fast = crate::kernel::search::FastOperationScope::enter("constructed output partition");
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(left.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap()
        .admit(right.clone(), ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let prepared = outputs
        .restore_entry_borrows(
            ResourceContext::new_with_equalities(&facts),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    let (joined, transfers) = prepared.finish(&facts).unwrap();
    assert_eq!(transfers.len(), 2);
    for ((expected, source), transfer) in [left, right]
        .iter()
        .zip(&outputs.occurrences)
        .zip(transfers)
    {
        assert_eq!(source.source, transfer.source);
        assert_eq!(
            joined.owned_fact_for_occurrence(transfer.destination),
            Some(expected)
        );
    }
}

#[test]
fn mixed_output_partition_does_not_recheck_restored_borrows_against_new_outputs() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, p, _, left, right) = partition();
    let retained = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p,
        32u32.into(),
        36u32.into(),
        1,
    ));
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(retained.clone());
    let _fast = crate::kernel::search::FastOperationScope::enter("mixed symbolic output partition");
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(left, ReturnOwnershipOrigin::EntryBorrow, &facts)
        .unwrap()
        .admit(right, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let prepared = outputs
        .restore_entry_borrows(
            frame.clone(),
            ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
            &facts,
        )
        .unwrap();
    let (joined, transfers) = prepared.finish(&facts).unwrap();
    assert_eq!(transfers.len(), 2);
    assert_eq!(joined.facts().len(), 3);
    assert!(joined.contains_exact_representation(&retained));
    assert_eq!(frame.facts().len(), 1);
}

#[test]
fn output_partition_refuses_unsupported_geometry_without_search_or_publication() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, p, _, left, right) = partition();
    let prefix = EvaluatedReturnResources::new(&facts)
        .admit(left, ReturnOwnershipOrigin::Description, &facts)
        .unwrap()
        .admit(right, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let third = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p,
        32u32.into(),
        36u32.into(),
        1,
    ));
    let original = prefix.resources.clone();
    let _fast = crate::kernel::search::FastOperationScope::enter("unsupported output partition");
    assert!(matches!(
        prefix.admit(third, ReturnOwnershipOrigin::Description, &facts),
        Err(ResourceContextValidityError::UnsupportedOwnershipBoundary)
    ));
    assert_eq!(original.facts().len(), 2);
}

#[test]
fn caller_boundary_refuses_missing_symbolic_evidence_without_search() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, p, _, left, _) = partition();
    let second = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p.clone(),
        32u32.into(),
        36u32.into(),
        1,
    ));
    let frame = ResourceContext::new_with_equalities(&facts).unchecked_with_facts([left, second]);
    let returned = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p,
        40u32.into(),
        44u32.into(),
        1,
    ));
    let _fast = crate::kernel::search::FastOperationScope::enter("unsupported retained boundary");
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(returned, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let prepared = outputs
        .restore_entry_borrows(
            frame.clone(),
            ReturnResourceComposition::ValidateDescriptions,
            &facts,
        )
        .unwrap();
    assert!(matches!(
        prepared.finish(&facts),
        Err(ResourceContextValidityError::UnsupportedOwnershipBoundary)
    ));
    assert_eq!(frame.facts().len(), 2);
}

#[test]
fn symbolic_composite_children_construct_a_partition_without_discovery() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, p, n, _, _) = partition();
    let expr = |value| ProgramExpression::Value(ProgramValue::Int32(value));
    let base = ProgramExpression::Value(ProgramValue::pointer(p));
    let definition = CompositeResourceDefinition::new(
        "symbolic_partition",
        vec![],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                base.clone(),
                expr(0u32.into()),
                expr(n.clone()),
            )),
            ResourceSpec::owned_memory(MemorySegment::new(base, expr(n), expr(16u32.into()))),
        ],
        vec![],
    );
    let _fast = crate::kernel::search::FastOperationScope::enter("symbolic constructed children");
    let outputs = EvaluatedReturnResources::new(&facts)
        .admit(
            ResourceFact::own_composite("symbolic_partition".into(), vec![]),
            ReturnOwnershipOrigin::Description,
            &facts,
        )
        .unwrap();
    let bodies = ConstructedReturnBodies::try_construct(
        &outputs,
        &[definition],
        &ExecutionState::new(),
        ReturnResourceComposition::ValidateDescriptions,
        &facts,
    )
    .unwrap();
    let body = bodies.get(outputs.occurrences[0].source).unwrap();
    assert_eq!(body.transfers.len(), 2);
}

#[test]
fn body_returns_use_actual_joint_custody_for_their_output_partition() {
    use crate::kernel::program_expression::{int32_literal, variable};
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_915_601));
    let q = Address::symbolic(Variable(8_915_602));
    let actual = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(p.clone()))
        .with_local("q", ProgramValue::pointer(q.clone()))
        .with_memory(
            SymbolicMemory::new()
                .with_block(p.base.clone(), 4)
                .with_block(q.base.clone(), 4),
        )
        .with_resource_context(
            ResourceContext::new_with_equalities(&facts).unchecked_with_facts([
                ResourceFact::own_memory(MemoryRange::new(p.clone(), 0u32.into(), 1u32.into())),
                ResourceFact::own_memory(MemoryRange::new(q.clone(), 0u32.into(), 1u32.into())),
            ]),
        );
    for (names, succeeds) in [(vec!["p", "q"], true), (vec!["p", "p"], false)] {
        let outputs = names
            .into_iter()
            .map(|name| {
                ResourceSpec::owned_memory(MemorySegment::new(
                    variable(name),
                    int32_literal(0),
                    int32_literal(1),
                ))
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post)
            })
            .collect();
        let function =
            program_function(ProgramType::Void, "body_partition", vec![], program_skip())
                .with_resource_summary(vec![], outputs);
        let result = evaluate_function_return_resources(
            &ResourceContext::new_with_equalities(&facts),
            &[],
            &[],
            &[],
            &[],
            &actual,
            &actual,
            &actual,
            &function,
            None,
            &ConsumedCellReturns::default(),
            &facts,
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        assert_eq!(result.is_ok(), succeeds);
        if let Ok(returned) = result {
            assert_eq!(returned.output_resources.facts().len(), 2);
        }
    }
}

#[test]
fn selected_frontier_returns_keep_output_carriers_and_refuse_reuse() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Address::symbolic(Variable(8_915_100));
    let q = Address::symbolic(Variable(8_915_101));
    let alias = Address::symbolic(Variable(8_915_102));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), alias.clone()), true);
    let range = |base| MemoryRange::new(base, 0u32.into(), 2u32.into());
    let mut plan = ConsumedCellReturns::default();
    plan.retain_frontier([range(p.clone()), range(q.clone())], &facts);
    let output = ResourceFact::own_memory(
        range(alias)
            .with_provenance(Arc::new(Address::symbolic(Variable(8_915_103))))
            .with_typed_carrier(),
    );
    let composition = ReturnResourceComposition::ApplyTransfers(&plan);
    for _ in 0..2 {
        let _fast = crate::kernel::search::FastOperationScope::enter("selected input footprint");
        let first = EvaluatedReturnResources::for_composition(composition, &facts)
            .admit_clause(
                output.clone(),
                ReturnOwnershipOrigin::Description,
                Some(0),
                Some(&plan),
                &facts,
            )
            .unwrap();
        assert!(matches!(
            first.occurrences[0].origin,
            ReturnOwnershipOrigin::ConsumedCell(_)
        ));
        let complete = first
            .admit_clause(
                ResourceFact::own_memory(range(q.clone())),
                ReturnOwnershipOrigin::Description,
                Some(1),
                Some(&plan),
                &facts,
            )
            .unwrap();
        // The inputs' partition, rather than spelling-based geometry, supplies
        // separation between these two symbolic output bases.
        let (returned, transfers) = complete
            .restore_entry_borrows(
                ResourceContext::new_with_equalities(&facts),
                composition,
                &facts,
            )
            .unwrap()
            .finish(&facts)
            .unwrap();
        assert_eq!(
            returned.owned_fact_for_occurrence(transfers[0].destination),
            Some(&output)
        );
        assert!(
            complete
                .admit_clause(
                    ResourceFact::own_memory(range(p.clone())),
                    ReturnOwnershipOrigin::Description,
                    Some(2),
                    Some(&plan),
                    &facts
                )
                .is_err()
        );
    }
    assert_eq!(plan.frontier.as_ref().unwrap().facts().len(), 2);
}

#[test]
fn static_and_dynamic_flat_selections_share_one_input_supply() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_915_200));
    let owner = ResourceFact::own_memory(MemoryRange::new(p, 0u32.into(), 2u32.into()));
    let (_, original) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([owner.clone()]);
    let selected = ConsumedCellReturn {
        input: original[0].1,
    };
    for dynamic_first in [false, true] {
        let mut plan = ConsumedCellReturns::default();
        plan.retain_frontier([owner.memory_own_range().unwrap().clone()], &facts);
        plan.direct.insert(1, selected);
        let composition = ReturnResourceComposition::ApplyTransfers(&plan);
        let roles = if dynamic_first {
            [
                (0, ReturnOwnershipOrigin::Description),
                (1, ReturnOwnershipOrigin::ConsumedCell(selected)),
            ]
        } else {
            [
                (1, ReturnOwnershipOrigin::ConsumedCell(selected)),
                (0, ReturnOwnershipOrigin::Description),
            ]
        };
        let first = EvaluatedReturnResources::for_composition(composition, &facts)
            .admit_clause(
                owner.clone(),
                roles[0].1,
                Some(roles[0].0),
                Some(&plan),
                &facts,
            )
            .unwrap();
        assert!(
            first
                .admit_clause(
                    owner.clone(),
                    roles[1].1,
                    Some(roles[1].0),
                    Some(&plan),
                    &facts
                )
                .is_err()
        );
    }
}

#[test]
fn return_coordinates_include_emitted_fields_but_defer_live_counts() {
    let comparison = |left| SpecProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right: SpecExpression::Value(ProgramValue::Int32(0u32.into())),
    };
    assert!(return_coordinate_ensure(&comparison(
        SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: Variable(8_915_300),
                children: Vec::new(),
                field_index: 0,
                at_entry: false,
            },
            program_type: ProgramType::Int32,
        }
    )));
    assert!(!return_coordinate_ensure(&comparison(
        SpecExpression::CountedResourceCount {
            name: "member".into(),
            arguments: Vec::new(),
        }
    )));
}
