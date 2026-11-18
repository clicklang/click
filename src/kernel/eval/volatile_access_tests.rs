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
    assert_eq!(
        mapped.value.native_compat(),
        &ProgramValue::Int32(MachineTerm::constant(9))
    );
}

#[path = "../../scaling_tests/kernel/eval/volatile_access_tests.rs"]
mod scaling_tests;

#[test]
fn volatile_local_write_retains_the_evaluated_value_root() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993671));
    let function = crate::kernel::program_function(
        ProgramType::Int32,
        "captured_write",
        vec![crate::kernel::program_parameter("dst", ProgramType::Int32).with_volatile(true)],
        ProgramStatement::Return(ProgramExpression::Variable("dst".into())),
    );
    let state = crate::kernel::functions::bind_program_function_arguments(
        &ExecutionState::new(),
        &function,
        &[ProgramValue::Int32(MachineTerm::constant(0))],
    )
    .unwrap()
    .with_retained_local("src", root.clone().into());
    let paths = super::statements::execute_program_lvalue_assignment_paths(
        &state,
        &ProgramExpression::Variable("dst".into()),
        &ProgramExpression::Variable("src".into()),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let event = paths[0]
        .facts
        .iter()
        .find_map(|fact| match fact.proposition() {
            Proposition::VolatileAccess(event) => Some(event),
            _ => None,
        })
        .expect("volatile write");
    assert_eq!(event.kind, VolatileAccessKind::Write);
    assert_eq!(event.value.root(), Some(&root));
}

#[test]
fn retained_volatile_read_values_keep_certification_and_nominal_event_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = KernelTerm::variable(
        KernelType::Program(ProgramType::Float32),
        Variable(10993672),
    );
    let event = volatile_access_fact(
        &mut ExecutionBudget::default(),
        VolatileAccessKind::Read,
        Address::symbolic(Variable(10993673)),
        ProgramType::Float32,
        crate::kernel::ExecutionValue::Shared(root.clone()),
    )
    .unwrap();
    assert_eq!(
        event.volatile_read_retained_result().unwrap().shared(),
        Some(&root)
    );
    let untrusted = ExecutionPureFact::new(event.proposition().clone());
    assert!(untrusted.volatile_read_retained_result().is_none());
}
