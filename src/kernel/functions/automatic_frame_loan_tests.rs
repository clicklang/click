use super::*;
use crate::kernel::loans::BorrowLedger;

#[test]
fn automatic_frame_retirement_checks_its_live_loans() {
    let function = program_function(
        ProgramType::Int32Pointer,
        "scope",
        vec![],
        program_return(crate::kernel::program_expression::addr_of("frame:holder")),
    );
    let state = ExecutionState::new().with_local("frame:holder", int32(0));
    let slot = state.locals.slot("frame:holder").unwrap().clone();
    let memory = SymbolicMemory::new().with_block(slot.base.clone(), 8);
    let state = state.with_memory(memory.clone());
    let backing = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        slot.offset_by_bytes(4),
        0u32.into(),
        1u32.into(),
        4,
    ));
    let support = ResourceContext::new()
        .unchecked_with_fact(backing.clone())
        .unique_owned_occurrence_for_fact(&backing)
        .unwrap()
        .0;
    let ledger = BorrowLedger::new();
    let lender = ledger.fresh_participant().unwrap();
    let borrower = ledger.fresh_participant().unwrap();
    let opening = ledger.lend(lender, borrower, support, backing).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let loaned = state.clone().with_loan_ledger(Some(ledger.clone()));
    let caller = ExecutionState::new();
    let returned = ProgramValue::typed_pointer(slot.clone(), ProgramType::Int32Pointer).into();
    for selected in [
        end_inline_frame_automatic_lifetimes(&loaned),
        end_function_body_automatic_lifetimes(&loaned, &function, caller.memory(), None),
        function_exit_memory(&caller, &loaned, &returned, &function),
    ] {
        assert!(matches!(selected, Err(RuntimeError::LoanRefusal(_))));
    }
    assert_eq!(
        end_function_body_automatic_lifetimes(&loaned, &function, &memory, None),
        Ok(memory),
    );
    let returned_share = ledger
        .transfer(opening.root_share, borrower, lender)
        .unwrap();
    let closing = ledger.apply(&returned_share).unwrap();
    let ended = closing
        .apply(&closing.end(opening.scope, lender).unwrap())
        .unwrap();
    let recovered = state.with_loan_ledger(Some(ended));
    assert!(
        !end_inline_frame_automatic_lifetimes(&recovered)
            .unwrap()
            .has_block(&slot.base)
    );
}
