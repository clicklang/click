//! Symbolic boundary checking retains endpoint evidence without discovery.
use super::*;

fn assert_without_discovery(operation: impl FnOnce()) {
    let _fast = crate::kernel::search::FastOperationScope::enter("symbolic boundary check");
    operation();
}

fn partition() -> (PureFactContext, ResourceFact, ResourceFact) {
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
    (facts, range(0u32.into(), n.clone()), range(n, 16u32.into()))
}

#[test]
fn fallback_inventory_raw_return_partition_checks_without_discovery() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, left, right) = partition();
    let prefix = || {
        EvaluatedReturnResources::new(&facts)
            .admit(left.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap()
    };
    // The shared symbolic endpoint directly establishes separation.
    assert!(
        prefix()
            .admit(right.clone(), ReturnOwnershipOrigin::Description, &facts)
            .is_ok()
    );
    assert_without_discovery(|| {
        prefix()
            .admit(right, ReturnOwnershipOrigin::Description, &facts)
            .unwrap();
    });
}

#[test]
fn fallback_inventory_pending_return_against_symbolic_frame_checks_without_discovery() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, left, right) = partition();
    let frame = ResourceContext::new_with_equalities(&facts)
        .try_compose_checked_ownership_and_occurrences([left], &facts)
        .unwrap()
        .0;
    let returned = EvaluatedReturnResources::new(&facts)
        .admit(right, ReturnOwnershipOrigin::Description, &facts)
        .unwrap();
    let prepare = || {
        returned
            .restore_entry_borrows(
                frame.clone(),
                ReturnResourceComposition::ApplyTransfers(&ConsumedCellReturns::default()),
                &facts,
            )
            .unwrap()
    };
    assert!(prepare().finish(&facts).is_ok());
    assert_without_discovery(|| {
        prepare().finish(&facts).unwrap();
    });
}

#[test]
fn fallback_inventory_constant_return_partition_is_already_search_free() {
    let _session = crate::kernel::VerificationSession::enter();
    let facts = PureFactContext::new();
    let p = Address::symbolic(Variable(8_915_010));
    let _fast = crate::kernel::search::FastOperationScope::enter("constant return control");
    let mut outputs = EvaluatedReturnResources::new(&facts);
    for (start, end) in [(0u32, 4u32), (4, 8)] {
        outputs = outputs
            .admit(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    p.clone(),
                    start.into(),
                    end.into(),
                    1,
                )),
                ReturnOwnershipOrigin::Description,
                &facts,
            )
            .unwrap();
    }
    assert_eq!(outputs.occurrences.len(), 2);
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
        .assume_condition(ConditionTerm::address_equal(p.clone(), alias.clone()), true);
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
                identity: InstanceId::from_variable(Variable(8_915_300)).into(),
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
