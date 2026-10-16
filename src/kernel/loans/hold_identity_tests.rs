use super::*;
use crate::kernel::{Pointer, PointerBlock, PointerOffsetTerm};

/// A hold must not compare equal to the state it restricts.
#[test]
fn holding_a_scope_mints_a_distinct_ledger_identity() {
    let base = Pointer {
        block: PointerBlock::Concrete("global:g".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = CResourceFact::own_memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(8),
    ));
    let context = ResourceContext::new().unchecked_with_fact(fact.clone());
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let (support, _) = context
        .unique_owned_occurrence_for_fact(&fact)
        .expect("memory backing");
    let opening = ledger
        .lend(owner, reader, support, fact.clone())
        .expect("the loan opens");
    let ledger = ledger.apply(&opening.transition).expect("the loan applies");
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: CResourceFact::View(fact.resource().clone()),
        hold: None,
    };
    let (with_hold, _) = ledger.hold(&binding, reader).expect("the hold opens");
    let without_hold = ledger.clone();
    assert_ne!(
        with_hold, without_hold,
        "a ledger with an active hold must differ from its hold-free predecessor"
    );
}
