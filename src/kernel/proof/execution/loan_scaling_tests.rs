use super::*;
use crate::kernel::loans::{LoanLedger, LoanViewBinding};
use crate::kernel::{PointerBlock, PointerOffsetTerm, int32};
use std::collections::BTreeSet;

/// The two largest adjacent ratios of a doubling series, the same
/// near-linear rule `src/scaling_tests/surface/tests/scaling_tests.rs` applies.
fn assert_near_linear(axis: &str, samples: &[(usize, usize)]) {
    assert!(
        samples[0].1 > 0,
        "{axis}: nothing was measured: {samples:?}"
    );
    for pair in samples.windows(2) {
        assert_eq!(pair[1].0, pair[0].0 * 2, "{axis}: {samples:?}");
    }
    for pair in samples.windows(2).skip(samples.len().saturating_sub(3)) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}"
        );
    }
}

/// One arm state and one interface successor that both carry `count`
/// occurrence-keyed bindings of a single shared loan. This is the shape a
/// proof reaches by exposing one child per unfold or observe: the binding
/// count follows the proof, while the loan and its ledger follow the
/// contract. The successor's resource context is rebuilt from the
/// declared clauses, so its occurrences are fresh and only the binding
/// content can connect it to the arm.
fn interface_join_states(count: usize) -> (CState, CState) {
    let support_fact = CResourceFact::own_token("shared_support".to_string(), Vec::new());
    let viewed = (0..count)
        .map(|index| CResourceFact::view_token(format!("child_{index}"), Vec::new()))
        .collect::<Vec<_>>();
    let resources = ResourceContext::new()
        .unchecked_with_facts(std::iter::once(support_fact.clone()).chain(viewed.iter().cloned()));
    let support = resources.owned_occurrences_for_fact(&support_fact)[0];
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    let opening = ledger
        .lend(owner, reader, support, support_fact)
        .expect("one shared loan backs every exposed child");
    let bindings = viewed
        .iter()
        .map(|fact| LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: fact.clone(),
            hold: None,
        })
        .collect::<Vec<_>>();
    let arm_dependencies = viewed
        .iter()
        .zip(&bindings)
        .map(|(fact, binding)| (resources.occurrences_for_fact(fact)[0], binding.clone()))
        .collect::<Vec<_>>();
    let arm = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader))
        .with_resource_context_and_loan_dependencies(resources, arm_dependencies);

    let successor_resources = ResourceContext::new().unchecked_with_facts(viewed.iter().cloned());
    let successor_dependencies = viewed
        .iter()
        .zip(&bindings)
        .map(|(fact, binding)| {
            (
                successor_resources.occurrences_for_fact(fact)[0],
                binding.clone(),
            )
        })
        .collect::<Vec<_>>();
    let successor = CState::new()
        .with_resource_context_and_loan_dependencies(successor_resources, successor_dependencies);
    (arm, successor)
}

/// A contract-input view over parameter memory: symbolic base offset, so
/// it never enters the concrete dyadic index and stays in its block's
/// unindexed bucket.
fn parameter_view(variable: u64) -> CResourceFact {
    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(variable)),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        4,
    ))
}

/// `count` live symbolic contract-input loans, all in one block.
fn symbolic_contract_input_ledger(count: usize) -> LoanLedger {
    let viewed = (0..count as u64).map(parameter_view).collect::<Vec<_>>();
    let resources = ResourceContext::new().unchecked_with_facts(viewed.iter().cloned());
    let mut ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().expect("holder identity");
    for fact in &viewed {
        let support = resources.occurrences_for_fact(fact)[0];
        let opening = ledger
            .borrowed_contract_input(holder, support, fact.clone(), None)
            .expect("a checked symbolic contract input");
        ledger = ledger
            .apply(&opening.transition)
            .expect("the input root applies");
    }
    assert!(ledger.has_active_memory_loans());
    ledger
}

/// `count` concrete cells in the same block those loans protect.
fn cells_in_the_symbolic_block(count: usize) -> CMemory {
    let mut memory = CMemory::new();
    for index in 0..count {
        memory = memory.store(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(4 * index as i64),
            },
            int32(0),
        );
    }
    memory
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/loan_scaling_tests.rs");
}
