//! Migrated output-partition and caller-boundary regression controls.
use super::*;

fn partition() -> (
    PureFactContext,
    Pointer,
    MachineTerm,
    ResourceFact,
    ResourceFact,
) {
    let p = Pointer::symbolic(Variable(8_915_000));
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
            ReturnResourceComposition::RestoreEntryBorrows,
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
