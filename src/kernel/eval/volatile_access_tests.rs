use super::*;

fn access(budget: &mut ExecutionBudget, kind: VolatileAccessKind) -> ExecutionPureFact {
    volatile_access_fact(
        budget,
        kind,
        Address::symbolic(Variable(800_001)),
        ProgramType::Int32,
        ProgramValue::Int32(MachineTerm::Variable(Variable(800_002))),
    )
    .unwrap()
}

#[test]
fn typed_accesses_keep_nominal_identity_and_read_results() {
    let mut budget = ExecutionBudget::default();
    let first = access(&mut budget, VolatileAccessKind::Read);
    let second = access(&mut budget, VolatileAccessKind::Read);
    let write = access(&mut budget, VolatileAccessKind::Write);
    assert_ne!(first, second);
    assert_ne!(first, write);
    assert_eq!(first.volatile_read_result(), second.volatile_read_result());
    assert!(write.volatile_read_result().is_none());
    assert!(first.proposition().is_kernel_authority());
    let Proposition::VolatileAccess(event) = first.proposition() else {
        panic!()
    };
    assert_eq!(event.value_type, ProgramType::Int32);
    assert_eq!(event.pointer, Address::symbolic(Variable(800_001)));
    assert_eq!(first.proposition().clone(), *first.proposition());
}

#[test]
fn predicate_spelling_and_uncertified_records_do_not_supply_read_results() {
    let legacy = ExecutionPureFact::certified(Proposition::Predicate {
        name: "__click_volatile_read_0".into(),
        arguments: vec![
            Term::ProgramValue(ProgramValue::pointer(Address::symbolic(Variable(800_001)))),
            Term::ProgramValue(ProgramValue::Int32(MachineTerm::constant(7))),
        ],
    });
    assert!(legacy.volatile_read_result().is_none());
    let event = access(&mut ExecutionBudget::default(), VolatileAccessKind::Read);
    let untrusted = ExecutionPureFact::new(event.proposition().clone());
    assert!(untrusted.volatile_read_result().is_none());
}

#[test]
fn substitution_reaches_operands_and_preserves_event_identity() {
    use crate::kernel::reasoning::{
        collect_proposition_bitvector_variables, substitute_bitvector_variable_in_proposition,
        substitute_pointer_variable_in_proposition,
    };
    let fact = access(&mut ExecutionBudget::default(), VolatileAccessKind::Read);
    let Proposition::VolatileAccess(original) = fact.proposition() else {
        panic!()
    };
    let mut variables = std::collections::BTreeSet::new();
    collect_proposition_bitvector_variables(fact.proposition(), &mut variables);
    assert_eq!(variables, [Variable(800_001), Variable(800_002)].into());
    let mapped = substitute_bitvector_variable_in_proposition(
        fact.proposition(),
        Variable(800_002),
        &MachineTerm::constant(9),
    );
    let mapped = substitute_pointer_variable_in_proposition(
        &mapped,
        Variable(800_001),
        &Address::symbolic(Variable(800_003)),
    );
    let Proposition::VolatileAccess(mapped) = mapped else {
        panic!()
    };
    assert_eq!(mapped.id, original.id);
    assert_eq!(mapped.kind, original.kind);
    assert_eq!(mapped.pointer, Address::symbolic(Variable(800_003)));
    assert_eq!(mapped.value, ProgramValue::Int32(MachineTerm::constant(9)));
}

#[path = "../../scaling_tests/kernel/eval/volatile_access_tests.rs"]
mod scaling_tests;
