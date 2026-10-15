use super::*;
use crate::kernel::PointerOffsetTerm;

fn scalar(name: &str) -> CResourceFact {
    CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        Pointer {
            block: name.into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0u32.into(),
        1u32.into(),
        4,
    ))
}

fn access(
    ledger: &LoanLedger,
    binding: &LocalReferenceBinding,
    holder: LoanParticipantId,
    resources: &ResourceContext,
) -> Result<(), LoanRefusal> {
    ledger.validate_local_reference_access(
        binding,
        holder,
        resources,
        &binding
            .backing
            .owned
            .memory_own_range()
            .unwrap()
            .start_pointer(),
        CType::Int32,
    )
}

fn register(
    ledger: &LoanLedger,
    holder: LoanParticipantId,
    resources: &ResourceContext,
    fact: &CResourceFact,
) -> (LocalReferenceBinding, LoanLedger) {
    let support = resources.unique_owned_occurrence_for_fact(fact).unwrap().0;
    let (root, transition) = ledger
        .register_local_reference(holder, resources, support, CType::Int32)
        .unwrap();
    let ledger = ledger.apply(&transition).unwrap();
    assert!(ledger.invariant_holds());
    (root, ledger)
}

fn fixture() -> (
    LoanLedger,
    LoanParticipantId,
    ResourceContext,
    LocalReferenceBinding,
) {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let fact = scalar("local:scalar");
    let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
    let (root, ledger) = register(&ledger, holder, &resources, &fact);
    (ledger, holder, resources, root)
}

#[test]
fn local_reference_child_suspends_parent_and_recovers_once_without_minting_ownership() {
    let (ledger, holder, resources, root) = fixture();
    let original_resources = resources.clone();
    assert_eq!(access(&ledger, &root, holder, &resources), Ok(()));
    let (child, birth) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let active = ledger.apply(&birth).unwrap();
    assert_eq!(
        access(&active, &root, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(access(&active, &child, holder, &resources), Ok(()));
    assert_eq!(
        active
            .borrow_local_reference(&root, holder, &resources)
            .unwrap_err(),
        LoanRefusal::ActiveDependency
    );
    let ending = active
        .recover_local_reference(&child, holder, &resources)
        .unwrap();
    let ended = active.apply(&ending).unwrap();
    assert_eq!(access(&ended, &root, holder, &resources), Ok(()));
    assert_eq!(
        access(&ended, &child, holder, &resources),
        Err(LoanRefusal::AlreadyRecovered)
    );
    assert_eq!(
        ended
            .recover_local_reference(&child, holder, &resources)
            .unwrap_err(),
        LoanRefusal::AlreadyRecovered
    );
    assert_eq!(
        ended.apply(&ending).unwrap_err(),
        LoanRefusal::StalePredecessor
    );
    assert_eq!(original_resources, resources);
}

#[test]
fn local_reference_nested_child_requires_inner_ending_first() {
    let (ledger, holder, resources, root) = fixture();
    let (outer, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    let (inner, open) = ledger
        .borrow_local_reference(&outer, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    assert_eq!(
        access(&ledger, &root, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        access(&ledger, &outer, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        ledger
            .recover_local_reference(&outer, holder, &resources)
            .unwrap_err(),
        LoanRefusal::ActiveDependency
    );
    assert_eq!(access(&ledger, &inner, holder, &resources), Ok(()));
    let ledger = ledger
        .apply(
            &ledger
                .recover_local_reference(&inner, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(access(&ledger, &outer, holder, &resources), Ok(()));
    assert_eq!(
        access(&ledger, &root, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    let ledger = ledger
        .apply(
            &ledger
                .recover_local_reference(&outer, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(access(&ledger, &root, holder, &resources), Ok(()));
}

#[test]
fn local_reference_disjoint_roots_keep_independent_custody() {
    let (ledger, holder, resources, root) = fixture();
    let neighbor = scalar("local:neighbor");
    let resources = resources.unchecked_with_fact(neighbor.clone());
    let (neighbor, ledger) = register(&ledger, holder, &resources, &neighbor);
    let (child, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    assert_eq!(access(&ledger, &neighbor, holder, &resources), Ok(()));
    let (other_child, open) = ledger
        .borrow_local_reference(&neighbor, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    let ledger = ledger
        .apply(
            &ledger
                .recover_local_reference(&child, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(access(&ledger, &root, holder, &resources), Ok(()));
    assert_eq!(
        access(&ledger, &neighbor, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(access(&ledger, &other_child, holder, &resources), Ok(()));
}

#[test]
fn local_reference_copied_child_identity_stays_stale_after_same_address_reborrow() {
    let (ledger, holder, resources, root) = fixture();
    let (child, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    let alias = child.clone();
    let ledger = ledger
        .apply(
            &ledger
                .recover_local_reference(&child, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    let (next, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    assert_ne!(alias.id, next.id);
    assert_eq!(alias.backing, next.backing);
    assert_eq!(
        access(&ledger, &alias, holder, &resources),
        Err(LoanRefusal::AlreadyRecovered)
    );
    assert_eq!(access(&ledger, &next, holder, &resources), Ok(()));
    assert_eq!(
        ledger
            .recover_local_reference(&alias, holder, &resources)
            .unwrap_err(),
        LoanRefusal::AlreadyRecovered
    );
}

#[test]
fn local_reference_wrong_holder_arena_pointer_and_type_are_refused() {
    let (ledger, holder, resources, root) = fixture();
    let wrong_holder = ledger.fresh_participant().unwrap();
    assert_eq!(
        access(&ledger, &root, wrong_holder, &resources),
        Err(LoanRefusal::WrongHolder)
    );
    let foreign = LoanLedger::new();
    assert_eq!(
        access(&foreign, &root, holder, &resources),
        Err(LoanRefusal::WrongArena)
    );
    let pointer = root
        .backing
        .owned
        .memory_own_range()
        .unwrap()
        .start_pointer();
    assert_eq!(
        ledger.validate_local_reference_access(
            &root,
            holder,
            &resources,
            &pointer.offset_by_bytes(4),
            CType::Int32
        ),
        Err(LoanRefusal::InvalidEvidence)
    );
    assert_eq!(
        ledger.validate_local_reference_access(&root, holder, &resources, &pointer, CType::UInt32),
        Err(LoanRefusal::InvalidEvidence)
    );
}

#[test]
fn local_reference_requires_exact_live_owned_occurrence_at_access_and_recovery() {
    let (ledger, holder, resources, root) = fixture();
    let (child, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    let replaced = ResourceContext::new().unchecked_with_fact(root.backing.owned.clone());
    assert_eq!(
        access(&ledger, &child, holder, &replaced),
        Err(LoanRefusal::MissingBacking)
    );
    assert_eq!(
        ledger
            .recover_local_reference(&child, holder, &replaced)
            .unwrap_err(),
        LoanRefusal::MissingBacking
    );
    let view = CResourceFact::view_memory(root.backing.owned.memory_own_range().unwrap().clone());
    let views = ResourceContext::new().unchecked_with_fact(view.clone());
    let support = views.occurrences_for_fact(&view)[0];
    assert_eq!(
        ledger
            .register_local_reference(holder, &views, support, CType::Int32)
            .unwrap_err(),
        LoanRefusal::MissingBacking
    );
    assert_eq!(
        access(&ledger, &child, holder, &ResourceContext::new()),
        Err(LoanRefusal::MissingBacking)
    );
}

#[test]
fn local_reference_registration_rejects_duplicate_or_unsupported_backing() {
    let (ledger, holder, resources, root) = fixture();
    assert_eq!(
        ledger
            .register_local_reference(holder, &resources, root.backing.support, CType::Int32)
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    assert_eq!(
        ledger
            .register_local_reference(
                holder,
                &resources,
                ResourceOccurrenceId::default(),
                CType::Int32
            )
            .unwrap_err(),
        LoanRefusal::MissingBacking
    );
    let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        Pointer {
            block: "local:array".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0u32.into(),
        2u32.into(),
        4,
    ));
    let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
    let support = resources.unique_owned_occurrence_for_fact(&fact).unwrap().0;
    assert_eq!(
        ledger
            .register_local_reference(holder, &resources, support, CType::Int32)
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    assert_eq!(
        ledger
            .register_local_reference(holder, &resources, support, CType::Int32Pointer)
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
}

#[test]
fn local_reference_root_retirement_waits_for_children_and_fresh_registration_has_new_identity() {
    let (ledger, holder, resources, root) = fixture();
    let (child, open) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let ledger = ledger.apply(&open).unwrap();
    assert_eq!(
        ledger
            .retire_local_reference_root(&root, holder, &resources)
            .unwrap_err(),
        LoanRefusal::ActiveDependency
    );
    assert_eq!(
        ledger
            .retire_local_reference_root(&child, holder, &resources)
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    let ledger = ledger
        .apply(
            &ledger
                .recover_local_reference(&child, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        ledger
            .recover_local_reference(&root, holder, &resources)
            .unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    let ledger = ledger
        .apply(
            &ledger
                .retire_local_reference_root(&root, holder, &resources)
                .unwrap(),
        )
        .unwrap();
    let (next, ledger) = register(&ledger, holder, &resources, &root.backing.owned);
    assert_ne!(root.id, next.id);
    assert_eq!(
        access(&ledger, &root, holder, &resources),
        Err(LoanRefusal::AlreadyRecovered)
    );
    assert_eq!(access(&ledger, &next, holder, &resources), Ok(()));
    assert!(!ledger.is_pristine());
}

#[test]
fn local_reference_transition_rejects_stale_predecessor_and_altered_child() {
    let (ledger, holder, resources, root) = fixture();
    let (child, first) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let (_, second) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let active = ledger.apply(&first).unwrap();
    assert_eq!(
        active.apply(&second).unwrap_err(),
        LoanRefusal::StalePredecessor
    );
    let mut ending = active
        .recover_local_reference(&child, holder, &resources)
        .unwrap();
    ending.evidence = LoanTransitionEvidence::RecoverLocalReference(root);
    assert_eq!(
        active.apply(&ending).unwrap_err(),
        LoanRefusal::InvalidEvidence
    );
    let mut forged = child.clone();
    forged.parent = None;
    assert_eq!(
        access(&active, &forged, holder, &resources),
        Err(LoanRefusal::InvalidEvidence)
    );
}

#[test]
fn local_reference_alternative_successors_cannot_exchange_child_bindings() {
    let (ledger, holder, resources, root) = fixture();
    let (left, left_birth) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let (right, right_birth) = ledger
        .borrow_local_reference(&root, holder, &resources)
        .unwrap();
    let left_ledger = ledger.apply(&left_birth).unwrap();
    let right_ledger = ledger.apply(&right_birth).unwrap();
    assert_ne!(left.id, right.id);
    assert_eq!(
        access(&right_ledger, &left, holder, &resources),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        left_ledger
            .recover_local_reference(&right, holder, &resources)
            .unwrap_err(),
        LoanRefusal::MissingLoanBinding
    );
    let ending = left_ledger
        .recover_local_reference(&left, holder, &resources)
        .unwrap();
    assert_eq!(
        right_ledger.apply(&ending).unwrap_err(),
        LoanRefusal::StalePredecessor
    );
    assert_eq!(
        left_ledger
            .recover_local_reference(&left, left_ledger.fresh_participant().unwrap(), &resources)
            .unwrap_err(),
        LoanRefusal::WrongHolder
    );
    assert!(left_ledger.invariant_holds());
    assert!(right_ledger.invariant_holds());
}

#[test]
fn local_reference_scalar_registration_checks_width_and_support_type() {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    for value_type in [CType::Int32, CType::UInt8, CType::UInt16, CType::UInt32] {
        let pointer = Pointer {
            block: format!("local:{value_type:?}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer.clone(),
            0u32.into(),
            1u32.into(),
            value_type.byte_width(),
        ));
        let resources = ResourceContext::new().unchecked_with_fact(fact.clone());
        let support = resources.unique_owned_occurrence_for_fact(&fact).unwrap().0;
        let (root, birth) = ledger
            .register_local_reference(holder, &resources, support, value_type)
            .unwrap();
        let active = ledger.apply(&birth).unwrap();
        assert_eq!(
            active.validate_local_reference_access(&root, holder, &resources, &pointer, value_type),
            Ok(())
        );
        assert_eq!(
            ledger
                .register_local_reference(holder, &resources, support, CType::Int64)
                .unwrap_err(),
            LoanRefusal::InvalidEvidence
        );
        let wrong_width = if value_type.byte_width() == 1 {
            CType::UInt16
        } else {
            CType::UInt8
        };
        assert_eq!(
            ledger
                .register_local_reference(holder, &resources, support, wrong_width)
                .unwrap_err(),
            LoanRefusal::InvalidEvidence
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/loans/local_references/tests.rs");
}
