//! Symbolic boundary checking retains endpoint evidence without discovery.
use super::*;

fn assert_without_discovery(operation: impl FnOnce()) {
    let _fast = crate::kernel::search::FastOperationScope::enter("symbolic boundary check");
    operation();
}

fn partition() -> (PureFactContext, ResourceFact, ResourceFact) {
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
    let p = Pointer::symbolic(Variable(8_915_010));
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
