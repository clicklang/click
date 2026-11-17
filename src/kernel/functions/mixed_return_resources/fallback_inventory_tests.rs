//! These probes intentionally demonstrate compatibility discovery, rather than
//! claiming that every call into a compatibility wrapper searches.
use super::*;

fn assert_ownership_discovery(operation: impl FnOnce()) {
    let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _fast = crate::kernel::search::FastOperationScope::enter("fallback inventory probe");
        operation();
    }))
    .expect_err("this compatibility route must still expose its discovery dependency");
    let message = failure
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| failure.downcast_ref::<&str>().copied())
        .expect("discovery guard panic text");
    assert!(
        message.contains("entered discovery ownership_validity_candidates"),
        "{message}"
    );
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
fn fallback_inventory_raw_return_partition_still_discovers() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, left, right) = partition();
    let prefix = || {
        EvaluatedReturnResources::new(&facts)
            .admit(left.clone(), ReturnOwnershipOrigin::Description, &facts)
            .unwrap()
    };
    // Valid adjacent symbolic ranges work today, through compatibility.
    assert!(
        prefix()
            .admit(right.clone(), ReturnOwnershipOrigin::Description, &facts)
            .is_ok()
    );
    assert_ownership_discovery(|| {
        let _ = prefix().admit(right, ReturnOwnershipOrigin::Description, &facts);
    });
}

#[test]
fn fallback_inventory_pending_return_against_symbolic_frame_still_discovers() {
    let _session = crate::kernel::VerificationSession::enter();
    let (facts, left, right) = partition();
    let frame = ResourceContext::new_with_equalities(&facts)
        .try_compose_with_legacy_discovery_and_occurrences([left], &facts)
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
    assert_ownership_discovery(|| {
        let _ = prepare().finish(&facts);
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
