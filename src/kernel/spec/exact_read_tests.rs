//! `exact(place)` evaluation (`design/exact-reads.md`): the read is named by
//! the selected program point, with no version walk; an ordinary read
//! names the cell's version point.

use super::*;

fn read(point: &str, value_type: ProgramType, exact: bool) -> SpecExpression {
    let cell = Address::new(point.into(), AddressOffset::constant(0));
    SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(ProgramValue::typed_pointer(
            cell,
            value_type.pointer_to().expect("a pointer to the cell"),
        ))),
        value_type,
        exact,
    }
}

fn evaluate(state: &ExecutionState, read: &SpecExpression) -> ProgramValue {
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        state,
        read,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
    )
    .unwrap();
    let [path] = paths.as_slice() else {
        panic!("one read path: {paths:?}")
    };
    assert!(path.obligations.is_empty());
    path.value.clone().into_native()
}

#[test]
fn an_exact_read_is_named_by_its_own_state_not_the_version_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Address::new("exact-read-cell".into(), AddressOffset::constant(0));
    let other = Address::new("exact-read-other".into(), AddressOffset::constant(0));
    let stored = SymbolicMemory::new()
        .with_block("exact-read-cell", 4)
        .with_block("exact-read-other", 4)
        .store(cell.clone(), int32(7));
    let after = stored.clone().store(other, int32(9));
    let ordinary = read("exact-read-cell", ProgramType::Int32, false);
    let exact = read("exact-read-cell", ProgramType::Int32, true);
    let stored = ExecutionState::new().with_memory(stored);
    let after = stored.clone().with_memory(after);
    let own_read = |state: &ExecutionState| {
        int32(OldMachineTerm::read_named(
            state.program_point().for_exact_read(),
            Box::new(cell.clone()),
            LoadKind::Int32,
        ))
    };

    assert_eq!(evaluate(&after, &ordinary), evaluate(&stored, &ordinary));
    assert_eq!(evaluate(&after, &exact), own_read(&after));
    assert_eq!(evaluate(&stored, &exact), own_read(&stored));
    assert_ne!(evaluate(&after, &exact), evaluate(&after, &ordinary));
    assert_ne!(evaluate(&after, &exact), evaluate(&stored, &exact));
}

#[test]
fn an_exact_pointer_read_has_its_own_read_as_provenance() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Address::new("exact-pointer-cell".into(), AddressOffset::constant(0));
    let other = Address::new("exact-pointer-other".into(), AddressOffset::constant(0));
    let after = SymbolicMemory::new()
        .with_block("exact-pointer-cell", 8)
        .with_block("exact-pointer-other", 4)
        .store(other, int32(9));
    let after = ExecutionState::new().with_memory(after);
    let state = intern_memory_ref(after.memory());
    let ProgramValue::Pointer(exact) = evaluate(
        &after,
        &read("exact-pointer-cell", ProgramType::Int32Pointer, true),
    ) else {
        panic!("a pointer read")
    };
    let source = exact
        .address()
        .as_loaded_value()
        .expect("pointer read source");
    assert_eq!(source.defining_address, cell);
    assert_eq!(source.point.read_version_id(), after.program_point_id());
    assert!(source.point.is_exact_read());
    assert_eq!(exact.provenance(), exact.address());
    assert_eq!(exact.bounds_owner(), Some(exact.address()));
    assert_eq!(exact.program_type(), ProgramType::Int32Pointer);

    // The ordinary read names the cell's version point instead.
    let ProgramValue::Pointer(ordinary) = evaluate(
        &after,
        &read("exact-pointer-cell", ProgramType::Int32Pointer, false),
    ) else {
        panic!("a pointer read")
    };
    assert_eq!(
        ordinary.address(),
        &Address::canonical_read(&state, None, &cell)
    );
    assert_ne!(ordinary.address(), exact.address());
}
