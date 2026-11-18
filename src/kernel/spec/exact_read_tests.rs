//! `exact(place)` evaluation (`design/exact-reads.md`): the read is named by
//! the selected state's own memory, with no version walk; an ordinary read
//! names the cell's version point.

use super::*;

fn read(point: &str, value_type: ProgramType, exact: bool) -> SpecExpression {
    let cell = Address {
        base: point.into(),
        offset: AddressOffset::Constant(0),
    };
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

fn evaluate(memory: &SymbolicMemory, read: &SpecExpression) -> ProgramValue {
    let state = ExecutionState::new().with_memory(memory.clone());
    let paths = evaluate_spec_expression_paths_with_loop_entry_in(
        &state,
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
    let cell = Address {
        base: "exact-read-cell".into(),
        offset: AddressOffset::Constant(0),
    };
    let other = Address {
        base: "exact-read-other".into(),
        offset: AddressOffset::Constant(0),
    };
    let stored = SymbolicMemory::new()
        .with_block("exact-read-cell", 4)
        .with_block("exact-read-other", 4)
        .store(cell.clone(), int32(7));
    let after = stored.clone().store(other, int32(9));
    let ordinary = read("exact-read-cell", ProgramType::Int32, false);
    let exact = read("exact-read-cell", ProgramType::Int32, true);
    let own_read = |memory: &SymbolicMemory| {
        int32(MachineTerm::memory_read(
            intern_memory_ref(memory),
            cell.clone(),
            LoadKind::Int32,
        ))
    };

    // The store to another object leaves the cell's version point: the
    // ordinary read after it is the read before it.
    assert_eq!(evaluate(&after, &ordinary), evaluate(&stored, &ordinary));
    // The exact read is named by the later state itself.
    assert_eq!(evaluate(&after, &exact), own_read(&after));
    assert_ne!(evaluate(&after, &exact), evaluate(&after, &ordinary));

    // Where the walk is trivial, the two forms are the same read.
    assert_eq!(evaluate(&stored, &exact), own_read(&stored));
    assert_eq!(evaluate(&stored, &exact), evaluate(&stored, &ordinary));
}

#[test]
fn an_exact_pointer_read_has_its_own_read_as_provenance() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Address {
        base: "exact-pointer-cell".into(),
        offset: AddressOffset::Constant(0),
    };
    let other = Address {
        base: "exact-pointer-other".into(),
        offset: AddressOffset::Constant(0),
    };
    let after = SymbolicMemory::new()
        .with_block("exact-pointer-cell", 8)
        .with_block("exact-pointer-other", 4)
        .store(other, int32(9));
    let state = intern_memory_ref(&after);
    let ProgramValue::Pointer(exact) = evaluate(
        &after,
        &read("exact-pointer-cell", ProgramType::Int32Pointer, true),
    ) else {
        panic!("a pointer read")
    };
    let own_read = Address::loaded_value(&state.unchanged_bytes_source(), &cell);
    assert_eq!(exact.address(), &own_read);
    assert_eq!(exact.provenance(), &own_read);
    assert_eq!(exact.bounds_owner(), Some(&own_read));
    assert_eq!(exact.program_type(), ProgramType::Int32Pointer);

    // The ordinary read names the cell's version point instead.
    let ProgramValue::Pointer(ordinary) = evaluate(
        &after,
        &read("exact-pointer-cell", ProgramType::Int32Pointer, false),
    ) else {
        panic!("a pointer read")
    };
    assert_eq!(ordinary.address(), &Address::canonical_read(&state, &cell));
    assert_ne!(ordinary.address(), exact.address());
}
