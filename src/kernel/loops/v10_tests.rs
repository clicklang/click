use super::*;

fn memory_range(base: u32, end: u32) -> CMemoryRange {
    CMemoryRange::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(base),
        Bitvector32Term::Constant(end),
    )
}

#[test]
fn loop_havoc_requires_a_checked_set_disjoint_from_active_loans() {
    let escrow = CResourceFact::own_memory(memory_range(0, 1));
    let support = ResourceContext::new()
        .unchecked_with_fact(escrow.clone())
        .unique_owned_occurrence_for_fact(&escrow)
        .expect("the test escrow has one backing occurrence")
        .0;
    let ledger = super::super::loans::LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let opening = ledger.lend(owner, owner, support, escrow).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();

    let assumptions = PureFactContext::new();
    assert!(validate_loop_havoc_stable_loans(&ledger, None, &assumptions).is_err());
    assert!(
        validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(0, 1)]), &assumptions)
            .is_err()
    );
    assert!(
        validate_loop_havoc_stable_loans(&ledger, Some(&[memory_range(2, 3)]), &assumptions)
            .is_ok()
    );
}

#[test]
fn owned_entry_footprint_names_memory_owners_and_refuses_unnameable_ones() {
    let empty = ResourceContext::new();
    assert_eq!(checked_owned_entry_footprint(&empty), Some(Vec::new()));

    let owned = CResourceFact::own_memory(memory_range(2, 3));
    let viewed = CResourceFact::view_memory(memory_range(0, 1));
    let memory_only = ResourceContext::new()
        .unchecked_with_fact(owned)
        .unchecked_with_fact(viewed);
    // A view lends no write authority, so it is not part of the footprint.
    assert_eq!(
        checked_owned_entry_footprint(&memory_only),
        Some(vec![memory_range(2, 3)])
    );

    // An owned resource whose bytes this level cannot enumerate leaves the
    // write set unknown, so the barrier stays closed rather than shrinking
    // to the memory owners that happen to be nameable.
    let folded = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(2, 3)))
        .unchecked_with_fact(CResourceFact::own(CResource::Token {
            name: "tokens".to_string(),
            arguments: Vec::new().into(),
        }));
    assert_eq!(checked_owned_entry_footprint(&folded), None);
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loops/v10_tests.rs");
}
