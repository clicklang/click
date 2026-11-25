use super::*;
use crate::kernel::{Address, OldAddressOffset, SymbolicMemory};

fn view(index: usize, end: u32) -> CheckedResourceFact {
    CheckedResourceFact {
        fact: ResourceFact::view_memory(MemoryRange::new(
            Address {
                base: format!("local:borrow-{index}").into(),
                offset: OldAddressOffset::Constant(0),
            },
            0.into(),
            end.into(),
        )),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
        mutex_storage: None,
    }
}

fn plan() -> StableViewTransferPlan {
    let ledger = BorrowLedger::new();
    plan_stable_view_transfer(
        &ResourceContext::new(),
        &[],
        &PureFactContext::new(),
        &ledger,
        ledger.fresh_participant().unwrap(),
        ledger.fresh_participant().unwrap(),
    )
    .unwrap()
}

#[test]
fn local_views_preserve_aliases_check_bounds_and_mint_no_owned_escrow() {
    let memory = SymbolicMemory::new().with_block(
        view(0, 2).fact.memory_range().unwrap().base().base.clone(),
        8,
    );
    let assumptions = PureFactContext::new();
    let mut plan = plan();
    plan.lend_local_views(&memory, &[view(0, 2), view(0, 1), view(0, 2)], &assumptions)
        .unwrap();
    assert!(plan.ledger.invariant_holds());
    assert_eq!(plan.stable_views.len(), 2);
    assert!(plan.escrowed_owners.is_empty());
    assert!(plan.caller_resources_after_requirements.is_empty());
    let entry = plan.ledger.clone();
    assert_eq!(plan.recheck_entry(plan.caller_ledger()).unwrap(), entry);
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(recovery.resources.is_empty());
    assert!(recovery.restorations.is_empty());
    assert!(recovery.terminal_ledger.invariant_holds());
    let mut outside = self::plan();
    assert!(
        outside
            .lend_local_views(&memory, &[view(0, 3)], &assumptions)
            .is_err()
    );
    let ended = memory.without_local_block(&view(0, 2).fact.memory_range().unwrap().base().base);
    assert!(
        outside
            .lend_local_views(&ended, &[view(0, 1)], &assumptions)
            .is_err()
    );
}

fn lend_memory(
    ledger: &BorrowLedger,
    lender: BorrowParticipantId,
    borrower: BorrowParticipantId,
    range: MemoryRange,
) -> BorrowOpening {
    let owner = ResourceFact::own_memory(range);
    let support = ResourceContext::new()
        .unchecked_with_fact(owner.clone())
        .unique_owned_occurrence_for_fact(&owner)
        .unwrap()
        .0;
    ledger.lend(lender, borrower, support, owner).unwrap()
}

#[test]
fn automatic_storage_retirement_uses_the_retained_backing_identity() {
    let slot = SymbolicMemory::local_lifetime_pointer(1, "buffer");
    let other = SymbolicMemory::local_lifetime_pointer(2, "buffer");
    let bound = OldMachineTerm::Variable(Variable(91));
    let symbolic = MemoryRange::new(Address::symbolic(Variable(90)), 0u32.into(), bound.clone())
        .with_provenance(Arc::new(slot.clone()));
    let ledger = BorrowLedger::new();
    let lender = ledger.fresh_participant().unwrap();
    let borrower = ledger.fresh_participant().unwrap();
    let empty = lend_memory(
        &ledger,
        lender,
        borrower,
        symbolic.with_bounds(symbolic.base().clone(), bound.clone(), bound),
    );
    let ledger = ledger.apply(&empty.transition).unwrap();
    assert!(
        ledger
            .automatic_storage_retirement_refusal(&slot.base, &16u32.into())
            .is_none()
    );

    let opening = lend_memory(&ledger, lender, borrower, symbolic.clone());
    let ledger = ledger.apply(&opening.transition).unwrap();
    let refusal = ledger
        .automatic_storage_retirement_refusal(&slot.base, &16u32.into())
        .expect("the symbolic spelling retains the automatic object's identity");
    assert_eq!(refusal.category(), BorrowRefusalCategory::ActiveDependency);
    assert_eq!(
        refusal.subject().conflicting_resource_fact(),
        Some(&ResourceFact::view_memory(symbolic)),
    );
    assert!(
        ledger
            .automatic_storage_retirement_refusal(&other.base, &16u32.into())
            .is_none()
    );
    let returned = ledger
        .transfer(opening.root_share, borrower, lender)
        .unwrap();
    let closing = ledger.apply(&returned).unwrap();
    let ended = closing
        .apply(&closing.end(opening.scope, lender).unwrap())
        .unwrap();
    assert!(
        ended
            .automatic_storage_retirement_refusal(&slot.base, &16u32.into())
            .is_none()
    );
    assert!(
        ledger
            .automatic_storage_retirement_refusal(&slot.base, &16u32.into())
            .is_some()
    );
    assert!(ledger.invariant_holds());
    assert!(ended.invariant_holds());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/borrows/local_storage_tests.rs");
}

#[test]
fn local_borrow_admission_distinguishes_overlap_from_missing_separation() {
    let requirement = view(0, 1);
    let range = requirement.fact.memory_range().unwrap();
    let memory = SymbolicMemory::new().with_block(range.base().base.clone(), 4);
    let backing = LocalViewBacking::check(&memory, &requirement.fact, &PureFactContext::new())
        .expect("one live local cell");
    let ledger = BorrowLedger::new();
    let lender = ledger.fresh_participant().unwrap();
    let borrower = ledger.fresh_participant().unwrap();
    let opening = lend_memory(&ledger, lender, borrower, range.clone());
    let overlapping = ledger.apply(&opening.transition).unwrap();
    assert_eq!(
        backing.check_admission(&overlapping, &PureFactContext::new()),
        Err(StableViewPlanError::Borrow(BorrowRefusal::ActiveDependency)),
    );

    let other = Address::symbolic(Variable(99_100));
    let known_alias = PureFactContext::new().assume_condition(
        crate::kernel::OldConditionTerm::address_equal(range.base().clone(), other.clone()),
        true,
    );
    let unrelated = MemoryRange::new(
        Address::symbolic(Variable(99_101)),
        0u32.into(),
        1u32.into(),
    );
    let opening = lend_memory(&ledger, lender, borrower, unrelated);
    let unrelated = ledger.apply(&opening.transition).unwrap();
    let requirement = unrelated.memory_access_requirement(range).unwrap();
    assert_eq!(
        backing.check_admission(&unrelated, &known_alias),
        Err(StableViewPlanError::UnestablishedLocalSeparation(Box::new(
            requirement.clone(),
        ))),
    );
    let stated = known_alias.assume_proposition(requirement);
    assert!(backing.check_admission(&unrelated, &stated).is_ok());
}
