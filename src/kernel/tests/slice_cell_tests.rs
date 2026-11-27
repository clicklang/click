//! Slice cells (`design/rust-slice-values.md`, step 2b-ii-a): a wide pointer
//! is stored as one 16-byte cell, a read of the cell at its slice type
//! returns the stored slice with its count, and every read that would take
//! one of the cell's words (a thin pointer, an integer, a byte) refuses until
//! a layout fact states them. A symbolic read of a slice cell (step 2b-ii-b)
//! names its data pointer and its count as reads of the one load, and the
//! read-over-write authority relates them to a stored slice.
use super::*;
use crate::kernel::VerificationSession;

fn count(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn wide(pointer: u64, length: u64) -> Pointer {
    Pointer::new(
        Address::symbolic(Variable(pointer)),
        ProgramType::UInt8Pointer,
    )
    .with_element_count(count(length))
}

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

fn cell(offset: i64) -> Address {
    Address::new(
        AddressBase::from("global:slice_cell"),
        AddressOffset::constant(offset),
    )
}

fn load(memory: &SymbolicMemory, offset: i64, value_type: ProgramType) -> ExpressionOutcome {
    let paths = evaluate_memory_load_paths(
        memory,
        cell(offset),
        value_type,
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
        false,
        false,
        None,
        None,
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    paths[0].outcome.clone()
}

/// A program store: it ends every cell it overlaps, as a C store does.
fn store(memory: SymbolicMemory, offset: i64, value: ProgramValue) -> SymbolicMemory {
    memory.store_retained_classed_with_context(
        cell(offset),
        value.into(),
        &PureFactContext::new(),
        None,
        None,
    )
}

fn refused(outcome: &ExpressionOutcome) -> bool {
    matches!(
        outcome,
        ExpressionOutcome::RuntimeError(RuntimeError::LoadTypeMismatch { .. })
    )
}

/// A slice stored in a cell reads back whole, count included, and a store
/// of another slice replaces it.
#[test]
fn a_stored_slice_reads_back_with_its_count() {
    let _session = VerificationSession::enter();
    let s = wide(961_000, 961_001);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s.clone()));
    let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = load(&memory, 0, bytes()) else {
        panic!("a slice read of a slice cell returns the slice");
    };
    assert_eq!(read, s);
    assert_eq!(read.len(), s.len());
    let t = wide(961_002, 961_003);
    let memory = memory.store(cell(0), ProgramValue::Pointer(t.clone()));
    assert_eq!(
        load(&memory, 0, bytes()),
        ExpressionOutcome::Value(ProgramValue::Pointer(t))
    );
}

/// No read takes one word of a slice cell: a thin pointer, an integer, a
/// byte, either word, or the cell at another slice type. Each refuses
/// rather than reading a word the kernel has no layout for.
#[test]
fn a_slice_cell_answers_no_partial_or_retyped_read() {
    let _session = VerificationSession::enter();
    let s = wide(961_010, 961_011);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s));
    for (offset, value_type) in [
        (0, ProgramType::UInt8Pointer),
        (0, ProgramType::VoidPointer),
        (0, ProgramType::UInt64),
        (8, ProgramType::UInt64),
        (8, ProgramType::UInt8Pointer),
        (0, ProgramType::Int32),
        (4, ProgramType::Int32),
        (12, ProgramType::UInt32),
        (9, ProgramType::UInt8),
        (0, ProgramType::SlicePointer(SliceElement::Str)),
    ] {
        let outcome = load(&memory, offset, value_type);
        assert!(refused(&outcome), "{offset} {value_type:?}: {outcome:?}");
    }
}

/// A store into either word of a slice cell ends the cell: the slice read
/// no longer returns the old slice. A slice stored over two pointer cells
/// ends both.
#[test]
fn a_store_into_a_slice_cell_ends_it() {
    let _session = VerificationSession::enter();
    let s = wide(961_020, 961_021);
    for (offset, value) in [
        (0, ProgramValue::UInt64(count(961_022))),
        (8, ProgramValue::UInt64(count(961_023))),
        (4, ProgramValue::Int32(count(961_024))),
    ] {
        let memory = store(
            store(SymbolicMemory::new(), 0, ProgramValue::Pointer(s.clone())),
            offset,
            value,
        );
        let outcome = load(&memory, 0, bytes());
        assert_ne!(
            outcome,
            ExpressionOutcome::Value(ProgramValue::Pointer(s.clone())),
            "a store at {offset} left the slice standing"
        );
    }
    let thin = |id| {
        ProgramValue::Pointer(Pointer::new(
            Address::symbolic(Variable(id)),
            ProgramType::UInt8Pointer,
        ))
    };
    let memory = store(
        store(
            store(SymbolicMemory::new(), 0, thin(961_025)),
            8,
            thin(961_026),
        ),
        0,
        ProgramValue::Pointer(s.clone()),
    );
    for (offset, old) in [(0, thin(961_025)), (8, thin(961_026))] {
        let outcome = load(&memory, offset, ProgramType::UInt8Pointer);
        assert_ne!(
            outcome,
            ExpressionOutcome::Value(old),
            "the slice store left a pointer cell at {offset} standing"
        );
    }
    assert_eq!(
        load(&memory, 0, bytes()),
        ExpressionOutcome::Value(ProgramValue::Pointer(s))
    );
}

/// The read-over-write authority answers no thin read of a slice cell: a
/// pointer read, a pointer-word read and a scalar read of the cell's state
/// each have no stored value, so no comparison form takes a slice's word.
#[test]
fn read_over_write_answers_no_thin_read_of_a_slice_cell() {
    let _session = VerificationSession::enter();
    let s = wide(961_030, 961_031);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s.clone()));
    let shared = crate::kernel::intern_memory(memory);
    assert_eq!(LoadKind::of_value(&ProgramValue::Pointer(s)), None);
    let read = Address::loaded_value(&shared, &cell(0));
    assert_eq!(
        crate::kernel::eval::pointer_read_over_write_program_value(&read),
        None
    );
    for kind in [LoadKind::Int32, LoadKind::Bits64] {
        let term = OldMachineTerm::read_named(ProgramPoint::unplaced(&shared), cell(0), kind);
        assert_eq!(crate::kernel::eval::read_over_write_value(&term), None);
    }
}

fn logical_load(memory: &SymbolicMemory, offset: i64, value_type: ProgramType) -> ExpressionPath {
    let paths = evaluate_logical_memory_load_paths(
        memory,
        cell(offset),
        value_type,
        Vec::new().into(),
        Vec::new(),
        &PureFactContext::new(),
    );
    assert_eq!(paths.len(), 1, "{paths:?}");
    paths[0].clone()
}

fn loaded_slice(path: &ExpressionPath) -> Pointer {
    let ExpressionOutcome::Value(ProgramValue::Pointer(read)) = &path.outcome else {
        panic!("a slice read is a slice: {:?}", path.outcome);
    };
    assert!(read.is_wide(), "{read:?}");
    read.clone()
}

/// A read of a slice cell memory says nothing about names the read: its data
/// pointer and its count are reads of the one load, not reads of either word
/// of the cell. Two reads of the unchanged cell are one slice; neither part
/// is the thin pointer read or the 64-bit read of a word.
#[test]
fn a_read_of_an_unknown_slice_cell_names_its_parts() {
    let _session = VerificationSession::enter();
    let memory = SymbolicMemory::new();
    let read = loaded_slice(&logical_load(&memory, 0, bytes()));
    assert_eq!(read, loaded_slice(&logical_load(&memory, 0, bytes())));
    let AddressBase::SliceData(load) = &read.address().base else {
        panic!("a slice read's data pointer is its own read: {read:?}");
    };
    assert_eq!(load.cell(), &cell(0));
    assert!(matches!(
        read.len(),
        Some(OldMachineTerm::MemoryLoad(_, count, LoadKind::SliceCount)) if count.load() == load
    ));
    let shared = crate::kernel::intern_memory(memory);
    assert_ne!(*read.address(), Address::loaded_value(&shared, &cell(0)));
    for offset in [0, 8] {
        let word = OldMachineTerm::read_named(
            ProgramPoint::unplaced(&shared),
            cell(offset),
            LoadKind::Bits64,
        );
        assert_ne!(read.len(), Some(&word));
    }
    // The slice type is kept; `str` and `[u8]` reads are reads of one load.
    let text = loaded_slice(&logical_load(
        &SymbolicMemory::new(),
        0,
        ProgramType::SlicePointer(SliceElement::Str),
    ));
    assert_eq!(
        text.program_type(),
        ProgramType::SlicePointer(SliceElement::Str)
    );
    assert_eq!(text.len(), read.len());
}

/// A logical read of a stored slice names its read, never the stored slice,
/// and the read-over-write authority relates the two: the whole read, its
/// data pointer and its count each resolve to the stored slice's, and the
/// read equation beside the read states it.
#[test]
fn a_logical_read_of_a_stored_slice_names_its_read() {
    let _session = VerificationSession::enter();
    let s = wide(961_040, 961_041);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s.clone()));
    let path = logical_load(&memory, 0, bytes());
    let read = loaded_slice(&path);
    assert_ne!(
        read, s,
        "a logical read lowers to the read, not the stored slice"
    );
    assert_eq!(
        crate::kernel::eval::slice_read_over_write_value(&read),
        Some(s.clone())
    );
    assert_eq!(
        crate::kernel::eval::read_over_write_value(read.len().unwrap()),
        s.len().cloned()
    );
    assert_eq!(
        crate::kernel::eval::pointer_read_over_write_program_value(read.address()),
        Some(s.as_ptr())
    );
    let equation = Proposition::condition_is(
        OldConditionTerm::pointer_equal(s.clone(), read.clone()),
        true,
    );
    assert!(
        path.facts
            .iter()
            .any(|fact| fact.proposition() == &equation),
        "{:?}",
        path.facts
    );
    let goal = Proposition::condition_is(OldConditionTerm::pointer_equal(read, s), true);
    assert!(crate::kernel::eval::holds_by_read_over_write(&goal));
}

/// The equality graph relates a slice read to the slice memory shows stored
/// in its cell, as it relates a pointer read to a stored pointer: asked about
/// the read's data pointer, it registers the read's stored slice.
#[test]
fn the_equality_graph_relates_a_slice_read_to_its_stored_slice() {
    let _session = VerificationSession::enter();
    let s = wide(961_050, 961_051);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s.clone()));
    let read = loaded_slice(&logical_load(&memory, 0, bytes()));
    let graph = crate::kernel::equality_graph::EqualityGraph::default();
    assert!(graph.are_equal(read.address(), s.address()));
    let unknown = loaded_slice(&logical_load(&SymbolicMemory::new(), 0, bytes()));
    assert!(!graph.are_equal(unknown.address(), s.address()));
}

/// A store into either word of a slice cell ends the stored slice for a
/// later read: the read names the new state and no authority resolves it.
#[test]
fn a_store_into_a_slice_cell_ends_its_read_over_write() {
    let _session = VerificationSession::enter();
    let s = wide(961_042, 961_043);
    for (offset, value) in [
        (0, ProgramValue::UInt64(count(961_044))),
        (8, ProgramValue::UInt64(count(961_045))),
    ] {
        let memory = store(
            store(SymbolicMemory::new(), 0, ProgramValue::Pointer(s.clone())),
            offset,
            value,
        );
        let read = loaded_slice(&logical_load(&memory, 0, bytes()));
        assert_eq!(
            crate::kernel::eval::slice_read_over_write_value(&read),
            None
        );
        assert_eq!(
            crate::kernel::eval::read_over_write_value(read.len().unwrap()),
            None
        );
    }
}

/// A thin read of a stored slice's first word is no read of the slice's
/// data pointer, and a slice read of a cell holding a thin pointer resolves
/// to nothing: neither crosses the layout the kernel does not state.
#[test]
fn slice_and_thin_reads_of_one_cell_stay_apart() {
    let _session = VerificationSession::enter();
    let thin = Pointer::new(
        Address::symbolic(Variable(961_046)),
        ProgramType::UInt8Pointer,
    );
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(thin));
    let read = loaded_slice(&logical_load(&memory, 0, bytes()));
    assert_eq!(
        crate::kernel::eval::slice_read_over_write_value(&read),
        None
    );
    assert_eq!(
        crate::kernel::eval::pointer_read_over_write_program_value(read.address()),
        None
    );
    assert_eq!(
        crate::kernel::eval::read_over_write_value(read.len().unwrap()),
        None
    );
}

/// A slice built from a read's parts with another count is no slice read:
/// the authority resolves only the whole read.
#[test]
fn only_a_whole_slice_read_resolves() {
    let _session = VerificationSession::enter();
    let s = wide(961_047, 961_048);
    let memory = SymbolicMemory::new().store(cell(0), ProgramValue::Pointer(s));
    let read = loaded_slice(&logical_load(&memory, 0, bytes()));
    let rebuilt = read.clone().with_replaced_element_count(count(961_049));
    assert_eq!(
        crate::kernel::eval::slice_read_over_write_value(&rebuilt),
        None
    );
}

/// A slice local is one 16-byte cell: an assignment stores the slice and a
/// read of the local returns it, count included.
#[test]
fn a_slice_local_holds_its_slice() {
    let _session = VerificationSession::enter();
    let execute = |state: &ExecutionState, statement: &ProgramStatement| {
        let paths = execute_execution_statement_paths(
            state,
            statement,
            &PureFactContext::new(),
            ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
            &mut ExecutionBudget::default(),
        )
        .expect("statement executes");
        assert_eq!(paths.len(), 1, "{:?}", paths);
        let StatementOutcome::Normal(state) = &paths[0].outcome else {
            panic!("{:?}", paths[0].outcome);
        };
        (**state).clone()
    };
    let state = execute(
        &ExecutionState::new(),
        &ProgramStatement::Declare {
            name: ("s".to_string()).into(),
            program_type: bytes(),
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            initializer: None,
            zero_fill: None,
            declared_class: None,
        },
    );
    let mut last = None;
    for (pointer, length) in [(961_050, 961_051), (961_052, 961_053)] {
        let s = wide(pointer, length);
        let assigned = execute(
            &state,
            &ProgramStatement::Assign {
                source: Default::default(),
                name: ("s".to_string()).into(),
                expression: ProgramExpression::Value(ProgramValue::Pointer(s.clone())),
                prior_result: None,
            },
        );
        let paths = evaluate_program_expression_paths(
            &assigned,
            &crate::kernel::program_expression::variable("s"),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1, "{paths:?}");
        assert_eq!(
            paths[0].outcome,
            ExpressionOutcome::Value(ProgramValue::Pointer(s.clone()))
        );
        last = Some((assigned, s));
    }
    // A second assignment replaces the first slice.
    let (assigned, s) = last.unwrap();
    let reassigned = execute(
        &assigned,
        &ProgramStatement::Assign {
            source: Default::default(),
            name: ("s".to_string()).into(),
            expression: ProgramExpression::Value(ProgramValue::Pointer(wide(961_054, 961_055))),
            prior_result: None,
        },
    );
    let paths = evaluate_program_expression_paths(
        &reassigned,
        &crate::kernel::program_expression::variable("s"),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_ne!(
        paths[0].outcome,
        ExpressionOutcome::Value(ProgramValue::Pointer(s))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/slice_cell_tests.rs");
}
