//! Access observations belong to read descriptors, not reserved variable names.
//! Capture/restore shares persistent roots; selected shared reads use an ID lookup.
use super::*;

type Key = (crate::kernel::program_point::ReadKey, Address, LoadKind);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct Id(u64);

#[derive(Clone)]
struct Record {
    point: ProgramPoint,
    pointer: Address,
    kind: LoadKind,
    origin: ProgramPoint,
    epoch: u64,
    bytes: u32,
    typed: bool,
    selected: bool,
}

#[derive(Clone, Default)]
pub(super) struct State {
    next: u64,
    keys: imbl::HashMap<Key, Id>,
    records: imbl::HashMap<Id, Record>,
    terms: imbl::HashMap<u64, Id>,
    latest: imbl::HashMap<(u64, Id), (ProgramPoint, Address)>,
}

thread_local! {
    static STATE: std::cell::RefCell<State> = Default::default();
}

pub(super) fn capture() -> State {
    STATE.with(|state| state.borrow().clone())
}

pub(super) fn restore(saved: &State) {
    STATE.with(|state| *state.borrow_mut() = saved.clone());
}

pub(super) fn clear() {
    STATE.with(|state| *state.borrow_mut() = State::default());
}

pub(super) fn existing(memory: &SharedMemory, pointer: &Address, kind: LoadKind) -> Option<Id> {
    existing_at(&ProgramPoint::at(memory), pointer, kind)
}

pub(super) fn existing_at(point: &ProgramPoint, pointer: &Address, kind: LoadKind) -> Option<Id> {
    crate::instrumentation::record_deterministic_work(1);
    STATE.with(|state| {
        state
            .borrow()
            .keys
            .get(&(point.read_key(), pointer.clone(), kind))
            .copied()
    })
}

pub(super) fn record(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    origin: &SharedMemory,
    bytes: u32,
) -> Id {
    record_at(
        &ProgramPoint::at(memory),
        pointer,
        kind,
        &ProgramPoint::at(origin),
        bytes,
    )
}

pub(super) fn record_at(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
    origin: &ProgramPoint,
    bytes: u32,
) -> Id {
    record_with_width(point, pointer, kind, origin, bytes, true)
}

pub(super) fn record_untyped(
    memory: &SharedMemory,
    pointer: &Address,
    kind: LoadKind,
    origin: &SharedMemory,
) -> Id {
    record_with_width(
        &ProgramPoint::at(memory),
        pointer,
        kind,
        &ProgramPoint::at(origin),
        kind.unrecorded_access_byte_width(),
        false,
    )
}

fn record_with_width(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
    origin: &ProgramPoint,
    bytes: u32,
    typed: bool,
) -> Id {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let key = (point.read_key(), pointer.clone(), kind);
        if let Some(id) = state.keys.get(&key).copied() {
            refresh_record(
                state.records.get_mut(&id).expect("recorded read"),
                origin,
                epoch,
                bytes,
                typed,
            );
            return id;
        }
        let id = Id(state.next);
        state.next = state
            .next
            .checked_add(1)
            .expect("read observation ID overflow");
        state.keys.insert(key, id);
        state.records.insert(
            id,
            Record {
                point: point.clone(),
                pointer: pointer.clone(),
                kind,
                origin: origin.clone(),
                epoch,
                bytes,
                typed,
                selected: false,
            },
        );
        id
    })
}

fn refresh_record(record: &mut Record, origin: &ProgramPoint, epoch: u64, bytes: u32, typed: bool) {
    let first_typed = typed && !record.typed;
    if first_typed {
        record.bytes = bytes;
    } else if typed {
        record.bytes = record.bytes.max(bytes);
    }
    record.typed |= typed;
    if record.epoch != epoch || first_typed {
        record.origin = origin.clone();
        record.epoch = epoch;
    }
}

pub(super) fn select(id: Id) {
    STATE.with(|state| {
        state
            .borrow_mut()
            .records
            .get_mut(&id)
            .expect("recorded read")
            .selected = true
    });
}

pub(super) fn selected(point: &ProgramPoint, pointer: &Address, kind: LoadKind) -> bool {
    existing_at(point, pointer, kind).is_some_and(|id| {
        STATE.with(|state| {
            state
                .borrow()
                .records
                .get(&id)
                .is_some_and(|read| read.selected)
        })
    })
}

pub(super) fn refresh(id: Id, origin: &ProgramPoint, bytes: u32) {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        refresh_record(
            state
                .borrow_mut()
                .records
                .get_mut(&id)
                .expect("registered read observation"),
            origin,
            epoch,
            bytes,
            true,
        )
    });
}

pub(super) fn produced(read: &MachineTerm, source: &MachineTerm) {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return;
    };
    let MachineTerm::MemoryLoad(origin, address, _) = source else {
        return;
    };
    if *kind != LoadKind::Bits64 {
        return;
    }
    let Some(id) = existing_at(memory, pointer, *kind) else {
        return;
    };
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow_mut()
            .latest
            .insert((epoch, id), (origin.clone(), address.as_ref().clone()));
    });
}

pub(super) fn latest(read: &MachineTerm) -> Option<MachineTerm> {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return None;
    };
    let id = existing_at(memory, pointer, *kind)?;
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow()
            .latest
            .get(&(epoch, id))
            .map(|(memory, pointer)| {
                crate::kernel::MachineTerm::read_named(memory.clone(), pointer.clone(), *kind)
            })
    })
}

pub(super) fn remember_term(term: &crate::kernel::KernelTerm, id: Id) {
    STATE.with(|state| {
        state.borrow_mut().terms.insert(term.id(), id);
    });
}

pub(super) fn bytes(id: Id) -> Option<u32> {
    STATE.with(|state| {
        state
            .borrow()
            .records
            .get(&id)
            .filter(|record| record.typed)
            .map(|record| record.bytes)
    })
}

pub(super) fn origin_for_cell(
    point: &ProgramPoint,
    pointer: &Address,
    kind: LoadKind,
) -> Option<SharedMemory> {
    let id = existing_at(point, pointer, kind)?;
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        let state = state.borrow();
        let record = state.records.get(&id)?;
        (record.epoch == epoch).then(|| record.origin.shared_memory().clone())
    })
}

pub(super) fn observation(id: Id) -> Option<ScalarReadObservation> {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow()
            .records
            .get(&id)
            .map(|record| ScalarReadObservation {
                point: record.point.clone(),
                pointer: record.pointer.clone(),
                kind: record.kind,
                bytes: record.bytes,
                origin: (record.epoch == epoch).then(|| record.origin.clone()),
            })
    })
}

pub(super) fn for_operand(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<ScalarReadObservation> {
    use crate::kernel::MachineOperandView;
    if let Some(variable) = operand.variable() {
        let id = LOAD_VARIABLE_REGISTRY
            .with(|registry| registry.borrow().get(variable).map(|read| read.observation))?;
        return observation(id);
    }
    if let MachineOperandView::Shared(term) = operand
        && let Some(id) = STATE.with(|state| state.borrow().terms.get(&term.id()).copied())
    {
        return observation(id);
    }
    let (point, pointer, kind) = operand.read_point()?;
    let memory = point.shared_memory();
    // Inspection is not an access observation. In particular, retaining the
    // conservative width of an unseen descriptor would widen a later typed
    // producer, and retaining this state would steal its first live origin.
    let Some(id) = existing_at(point, pointer, kind) else {
        return Some(ScalarReadObservation {
            point: point.clone(),
            pointer: pointer.clone(),
            kind,
            bytes: load_term_access_width(memory, pointer, kind),
            origin: Some(point.clone()),
        });
    };
    if let MachineOperandView::Shared(term) = operand {
        remember_term(term, id);
    }
    observation(id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTerm, MachineOperandView, VerificationSession};

    #[test]
    fn indexed_read_retains_its_observation_point() {
        let _session = VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let local = SymbolicMemory::local_pointer("unrelated");
        let state = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(local.base, 4));
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let origin = state.program_point();
        let version = origin
            .entry_integer_version(&pointer, LoadKind::Int32)
            .expect("the unrelated block leaves the caller's cell at entry");
        assert_ne!(origin.id(), version.id());

        let path = evaluate_indexed_read(
            version,
            &origin,
            pointer,
            ProgramType::Int32,
            ExecutionFacts::new(),
            vec![],
        );
        let ExpressionOutcome::Value(ProgramValue::Int32(read)) = path.outcome else {
            panic!("one symbolic word read");
        };
        let observed = for_operand(MachineOperandView::Legacy(&read)).unwrap();
        assert_eq!(observed.point.read_version_id(), entry.program_point_id());
        assert_eq!(observed.origin.and_then(|point| point.id()), origin.id());
    }

    #[test]
    fn cell_origin_lookup_preserves_float_width_and_epoch() {
        let _session = VerificationSession::enter();
        let address = Address::symbolic(Variable(998_708));
        let memory = intern_memory(SymbolicMemory::new());
        let origin = intern_memory(SymbolicMemory::new().with_block("float-origin", 8));
        let point = ProgramPoint::at(&memory);
        record_at(
            &point,
            &address,
            LoadKind::Float32,
            &ProgramPoint::at(&origin),
            4,
        );
        assert_eq!(
            origin_for_cell(&point, &address, LoadKind::Float32),
            Some(origin)
        );
        assert_eq!(origin_for_cell(&point, &address, LoadKind::Float64), None);
        begin_load_origin_epoch();
        assert_eq!(origin_for_cell(&point, &address, LoadKind::Float32), None);
    }

    #[test]
    fn a_typed_producer_replaces_an_untyped_canonical_reads_guessed_width() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(998_709));
        let untyped = canonical_scalar_read(&crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            LoadKind::Int32,
        ));
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&untyped))
                .unwrap()
                .bytes,
            8
        );
        record_load_access_width(memory.memory(), &pointer, 4);
        let typed = canonical_scalar_read(&crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            LoadKind::Int32,
        ));
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&typed))
                .unwrap()
                .bytes,
            4
        );
        // A genuine wider observation remains conservative when a narrower
        // producer later names the same descriptor.
        let MachineTerm::MemoryLoad(selected, address, kind) = &typed else {
            unreachable!()
        };
        record(selected.shared_memory(), address, *kind, &memory, 8);
        record(selected.shared_memory(), address, *kind, &memory, 4);
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&typed))
                .unwrap()
                .bytes,
            8
        );
    }

    #[test]
    fn inspecting_an_unobserved_read_does_not_capture_its_width_or_origin() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(998_707));
        let read = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            LoadKind::Int32,
        );
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&read))
                .unwrap()
                .bytes,
            8
        );
        assert!(existing(&memory, &pointer, LoadKind::Int32).is_none());
        let live = intern_memory(memory.memory().clone().store(
            pointer.offset_by_bytes(16),
            ProgramValue::Int32(1u32.into()),
        ));
        record(&memory, &pointer, LoadKind::Int32, &live, 4);
        let observed = for_operand(MachineOperandView::Legacy(&read)).unwrap();
        assert_eq!(observed.bytes, 4);
        assert_eq!(observed.origin, Some(ProgramPoint::at(&live)));
    }

    fn cyclic_frame_read(index: u64) -> (Proposition, Variable) {
        let pointer = Address {
            base: format!("local:frame-origin-{index}").into(),
            offset: AddressOffset::Constant(0),
        };
        let memory = intern_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 4));
        let read = crate::kernel::MachineTerm::read_named(
            ProgramPoint::at(&memory),
            pointer.clone(),
            LoadKind::Int32,
        );
        let bound = Variable(998_800 + index);
        let range = MemoryRange::new_with_element_width(
            Address {
                base: "frame-target".into(),
                offset: AddressOffset::Constant(0),
            },
            0u32.into(),
            MachineTerm::add_at(
                MachineIntegerType::Int32,
                read.clone(),
                MachineTerm::Variable(bound),
            ),
            4,
        );
        let origin = intern_memory(memory.memory().clone().with_call_memory_havoc(
            Variable(999_800 + index),
            &[range],
            &PureFactContext::new(),
            None,
        ));
        // The local read survives a havoc of another block. Its live origin
        // contains a range bound that refers to the same structural version.
        record(&memory, &pointer, LoadKind::Int32, &origin, 4);
        (
            Proposition::condition_is(ConditionTerm::equal(read, 0u32.into()), true),
            bound,
        )
    }

    #[test]
    fn frame_collection_terminates_on_cyclic_observation_origins_and_keeps_bounds() {
        let _session = VerificationSession::enter();
        let (proposition, bound) = cyclic_frame_read(0);
        let collect = || {
            let mut variables = std::collections::BTreeSet::new();
            crate::kernel::reasoning::variable_collection::collect_proposition_frame_variables(
                &proposition,
                &mut variables,
            );
            variables
        };
        let first = collect();
        assert!(first.contains(&bound));
        assert_eq!(collect(), first, "visited states belong to one collection");
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn structural_observations_need_no_reserved_name_and_restore_branch_metadata() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(SymbolicMemory::new());
        let pointer = Address::symbolic(Variable(998_701));
        let read = KernelTerm::scalar_read_descriptor(
            MachineIntegerType::Int32,
            &crate::kernel::ProgramPoint::at(&memory),
            &pointer,
            LoadKind::Int32,
        )
        .unwrap();
        let id = record(&memory, &pointer, LoadKind::Int32, &memory, 4);
        remember_term(&read, id);
        let observe = |read: &KernelTerm| for_operand(MachineOperandView::Shared(read)).unwrap();
        assert_eq!(load_variable_registry_len(), 0);
        assert_eq!(observe(&read).bytes, 4);
        let other_format = read.with_machine_observation_type(MachineIntegerType::UInt32);
        assert_eq!(observe(&other_format).bytes, 4);
        let saved = capture_load_variable_registry();
        begin_load_origin_epoch();
        assert!(observe(&other_format).origin.is_none());
        let later = intern_memory(memory.memory().clone().store(
            pointer.offset_by_bytes(16),
            ProgramValue::Int32(1u32.into()),
        ));
        record(&memory, &pointer, LoadKind::Int32, &later, 8);
        assert_eq!(observe(&read).bytes, 8);
        assert_eq!(
            observe(&other_format).origin,
            Some(ProgramPoint::at(&later))
        );
        restore_load_variable_registry(&saved);
        assert_eq!(observe(&read).bytes, 4);
        assert_eq!(
            observe(&other_format).origin,
            Some(ProgramPoint::at(&memory))
        );
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn equal_memory_at_distinct_points_does_not_share_access_observations() {
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let first = ProgramPoint::starting_at(&memory).for_exact_read();
        let second = ProgramPoint::starting_at(&memory).for_exact_read();
        let pointer = Address::symbolic(Variable(998_707));
        let kind = LoadKind::Bits64;
        assert_eq!(first.shared_memory(), second.shared_memory());
        let first_id = record_at(&first, &pointer, kind, &first, 4);
        let second_id = record_at(&second, &pointer, kind, &second, 8);
        assert_ne!(first_id, second_id);
        let first_read = crate::kernel::MachineTerm::read_named(first, pointer.clone(), kind);
        let second_read = crate::kernel::MachineTerm::read_named(second, pointer, kind);
        let observe = |read| for_operand(MachineOperandView::Legacy(read)).unwrap().bytes;
        assert_eq!(observe(&first_read), 4);
        assert_eq!(observe(&second_read), 8);
        produced(&first_read, &second_read);
        assert_eq!(latest(&first_read), Some(second_read.clone()));
        assert_eq!(latest(&second_read), None);
    }

    #[test]
    fn structural_observations_distinguish_read_kind_and_state() {
        let _session = VerificationSession::enter();
        let pointer = Address::symbolic(Variable(998_702));
        let before = intern_memory(SymbolicMemory::new());
        let after = intern_memory(
            SymbolicMemory::new().store(pointer.clone(), ProgramValue::Int32(1u32.into())),
        );
        let first = record(&before, &pointer, LoadKind::Int32, &before, 4);
        let other_kind = record(&before, &pointer, LoadKind::Int16, &before, 2);
        let other_time = record(&after, &pointer, LoadKind::Int32, &after, 8);
        assert_ne!(first, other_kind);
        assert_ne!(first, other_time);
        assert_eq!(bytes(first), Some(4));
        assert_eq!(bytes(other_kind), Some(2));
        assert_eq!(bytes(other_time), Some(8));
        let narrow_access = record(
            &before,
            &pointer.offset_by_bytes(16),
            LoadKind::Int32,
            &before,
            2,
        );
        assert_eq!(bytes(narrow_access), Some(2));
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn ordinary_integer_producers_retain_reads_without_reserved_variables() {
        let _session = VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let pointer = Address::symbolic(Variable(998_704));
        for ty in [
            ProgramType::Int8,
            ProgramType::UInt8,
            ProgramType::Int16,
            ProgramType::UInt16,
            ProgramType::Int32,
            ProgramType::UInt32,
            ProgramType::Int64,
            ProgramType::UInt64,
            ProgramType::Int128,
            ProgramType::UInt128,
        ] {
            let mut facts = ExecutionFacts::new();
            let value = canonicalized_symbolic_load_value_with_identity(
                &memory,
                None,
                &pointer,
                ty,
                &mut facts,
                &PureFactContext::new(),
                None,
                LoadPurpose::Logical,
            )
            .expect("integer read");
            let read =
                crate::kernel::spec::program_value_bitvector_term(&value).expect("scalar term");
            let MachineTerm::MemoryLoad(retained_state, address, kind) = &read else {
                panic!("{ty:?} must retain its read: {read:?}");
            };
            assert_eq!(address.as_ref(), &pointer);
            assert_eq!(
                canonical_form_of_load(
                    retained_state.shared_memory().clone(),
                    pointer.clone(),
                    *kind
                ),
                read
            );
            assert!(facts.is_empty());
            assert_eq!(load_variable_registry_len(), 0);
        }
    }

    #[test]
    fn selecting_a_read_keeps_its_address_when_another_read_was_stored_there() {
        let _session = VerificationSession::enter();
        let source = Address::symbolic(Variable(998_705));
        let destination = Address::symbolic(Variable(998_706));
        let memory = intern_memory(SymbolicMemory::new());
        let held = canonical_form_of_load(memory.clone(), source, LoadKind::Int32);
        let after = intern_memory(
            memory
                .memory()
                .clone()
                .store(destination.clone(), ProgramValue::Int32(held.clone())),
        );
        let read = canonical_form_of_load(after, destination.clone(), LoadKind::Int32);
        assert!(
            matches!(&read, MachineTerm::MemoryLoad(_, pointer, LoadKind::Int32) if **pointer == destination)
        );
        assert_ne!(read, held);
        assert_eq!(read_over_write_value(&read), Some(held));
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/eval/memory_loads/read_observations/tests.rs");
    }
}
