use super::*;

#[test]
fn external_displacements_and_heap_indexes_use_only_their_selected_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let parameter = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Variable(Variable(38_151)).into(),
    };
    let other_parameter = OldAddress {
        offset: OldAddressOffset::Variable(Variable(38_152)).into(),
        ..parameter.clone()
    };
    let heap = OldAddress {
        base: AddressBase::Heap(38_153),
        offset: OldAddressOffset::Constant(0).into(),
    };
    let start =
        ExecutionState::new().with_memory(SymbolicMemory::new().with_block(heap.base.clone(), 8));
    let store = |state: &ExecutionState, address: &OldAddress, bits| {
        state.clone().with_memory(state.memory().clone().store(
            address.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(bits)),
        ))
    };
    let p_written = store(&start, &parameter, 1);
    let h_written = store(&p_written, &heap, 2);
    let sibling = parameter.offset_by_bytes(4);
    let mut samples = Vec::new();
    for count in [4, 64, 1024] {
        let mut state = h_written.clone();
        for bits in 0..count {
            state = store(&state, &sibling, bits);
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let point = state.program_point();
            for (address, written) in [(&parameter, &p_written), (&heap, &h_written)] {
                assert_eq!(
                    point
                        .indexed_integer_version(address, LoadKind::Int32)
                        .and_then(|source| source.read_version_id()),
                    written.program_point_id(),
                );
            }
            assert!(
                point
                    .indexed_integer_version(&other_parameter, LoadKind::Int32)
                    .is_none()
            );
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );

    let aliased = store(&h_written, &other_parameter, 3);
    assert!(
        aliased
            .program_point()
            .indexed_integer_version(&parameter, LoadKind::Int32)
            .is_none()
    );
    assert!(
        aliased
            .program_point()
            .indexed_integer_version(&heap, LoadKind::Int32)
            .is_some()
    );

    let symbolic_heap = OldAddress {
        base: heap.base.clone(),
        offset: parameter.offset.clone(),
    };
    let indexed = store(&h_written, &symbolic_heap, 4);
    let point = indexed.program_point();
    assert!(
        point
            .indexed_integer_version(&heap, LoadKind::Int32)
            .is_none()
    );
    assert_eq!(
        point
            .indexed_integer_version(&symbolic_heap, LoadKind::Int32)
            .and_then(|source| source.read_version_id()),
        indexed.program_point_id(),
    );
}

#[test]
fn sealed_batch_read_lookup_ignores_the_number_of_effects() {
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let first = slot();
        let second = first.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(first.base.clone(), 4 * (count + 1)));
        let written = stored(&start, 7);
        let mut memory = written.memory().clone();
        for index in 1..=count {
            memory = memory.store(
                first.offset_by_bytes(index * 4),
                ProgramValue::Int32(OldMachineTerm::constant(index)),
            );
        }
        let (sealed, seal_work) = crate::instrumentation::measure_deterministic_work(|| {
            written.clone().with_memory(memory)
        });
        let ((older, newer), read_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                let point = sealed.program_point();
                (
                    point
                        .indexed_integer_version(&first, LoadKind::Int32)
                        .unwrap(),
                    point
                        .indexed_integer_version(&second, LoadKind::Int32)
                        .unwrap(),
                )
            });
        assert_eq!(older.read_version_id(), written.program_point_id());
        assert_eq!(newer.read_version_id(), sealed.program_point_id());
        assert_eq!(
            newer.indexed_integer_store_bits(),
            Some(&OldMachineTerm::constant(1))
        );
        samples.push((count, seal_work, read_work));
    }
    assert!(
        samples.iter().all(|&(count, seal, read)| {
            seal <= samples[0].1 + count as usize * 32 && read == samples[0].2
        }),
        "{samples:?}"
    );
}

#[test]
fn joining_one_changed_cell_uses_shared_index_branches() {
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 4 * (count + 1)));
        let mut memory = start.memory().clone();
        for index in 0..count {
            memory = memory.store(
                slot.offset_by_bytes(4 * index),
                ProgramValue::Int32(OldMachineTerm::constant(index)),
            );
        }
        let mut current = start.with_memory(memory);
        let original = current.program_point_id();
        let changed = slot.offset_by_bytes(4 * count);
        for _ in 0..8 {
            let write = |value| {
                current.clone().with_memory(current.memory().clone().store(
                    changed.clone(),
                    ProgramValue::Int32(OldMachineTerm::constant(value)),
                ))
            };
            let left = write(1);
            let right = write(2);
            let mut joined = left.clone();
            let ((), work) = crate::persistent::measure_persistent_work(|| {
                joined.join_program_points(&left, &right, current.path_link());
            });
            assert_eq!(
                joined
                    .program_point()
                    .indexed_integer_version(&slot, LoadKind::Int32)
                    .and_then(|point| point.read_version_id()),
                original
            );
            assert!(
                joined
                    .program_point()
                    .indexed_integer_version(&changed, LoadKind::Int32)
                    .is_none()
            );
            samples.push((count, work));
            current = joined;
        }
    }
    assert!(
        samples
            .iter()
            .all(|&(_, work)| work <= 8 * samples[0].1 + 32),
        "{samples:?}"
    );
}

#[test]
fn sealing_checked_footprints_ignores_cells_in_untouched_objects() {
    let mut samples = Vec::new();
    for count in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let target = OldAddress {
            base: "local:target".into(),
            offset: OldAddressOffset::Constant(0).into(),
        };
        let start = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block(slot.base.clone(), 4 * count)
                .with_block(target.base.clone(), 4),
        );
        let mut memory = start.memory().clone();
        for index in 0..count {
            memory = memory.store(
                slot.offset_by_bytes(4 * index),
                ProgramValue::Int32(OldMachineTerm::constant(index)),
            );
        }
        let written = start.with_memory(memory);
        let original = written.program_point_id();
        let ranges = [MemoryRange::new(target, 0.into(), 1.into())];
        let mut call_memory = written.memory().clone().with_call_memory_havoc(
            Variable(38_131),
            &ranges,
            &PureFactContext::new(),
            None,
        );
        let mut loop_memory = written
            .memory()
            .clone()
            .with_loop_memory_havoc_preserving_borrows(
                Variable(38_132),
                &std::collections::BTreeSet::from([slot.base.clone()]),
                Some(&ranges),
                None,
            );
        // Measure sealing the already prepared effects, including the indexed
        // lookup. Building the legacy memory views is a separate operation.
        let call_steps = call_memory.pending_steps.take();
        let loop_steps = loop_memory.pending_steps.take();
        let call_view = intern_memory_ref(&call_memory);
        let loop_view = intern_memory_ref(&loop_memory);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let called = written.path_link().after(call_view, call_steps);
            let head = written.path_link().after_loop_head(loop_view, loop_steps);
            for (path, memory) in [(called, &call_memory), (head, &loop_memory)] {
                assert_eq!(
                    ProgramPoint::of_state(memory, &path)
                        .indexed_integer_version(&slot, LoadKind::Int32)
                        .and_then(|point| point.read_version_id()),
                    original
                );
            }
        });
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|&(_, work)| work == samples[0].1),
        "{samples:?}"
    );
}

#[test]
fn complete_parameter_pointer_reads_keep_their_write_point_across_sibling_stores() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Variable(Variable(38_154)).into(),
    };
    let target = OldAddress::symbolic(Variable(38_155));
    let stored = OldPointer::new(target.clone(), ProgramType::Int32Pointer)
        .with_bounds(Some(SubobjectBounds::constant(target, 4)));
    let state = ExecutionState::new();
    let written = state.clone().with_memory(
        state
            .memory()
            .clone()
            .store(cell.clone(), ProgramValue::Pointer(stored.clone())),
    );
    let mut samples = Vec::new();
    for count in [4, 64, 1024] {
        let mut state = written.clone();
        for bits in 0..count {
            state = state.clone().with_memory(state.memory().clone().store(
                cell.offset_by_bytes(8),
                ProgramValue::Int32(OldMachineTerm::constant(bits)),
            ));
        }
        let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
            state
                .program_point()
                .indexed_typed_version(&cell, stored.program_type())
                .expect("complete pointer store at the parameter cell")
        });
        assert_eq!(version.read_version_id(), written.program_point_id());
        let read = OldPointer::from_point_read(version, stored.program_type(), &cell);
        assert_eq!(
            crate::kernel::eval::pointer_read_over_write_program_value(read.address()).as_ref(),
            Some(&stored)
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );

    let partial = written.clone().with_memory(written.memory().clone().store(
        cell.offset_by_bytes(4),
        ProgramValue::Int32(OldMachineTerm::constant(0)),
    ));
    assert!(
        partial
            .program_point()
            .indexed_typed_version(&cell, stored.program_type())
            .is_none()
    );
}

#[test]
fn boolean_and_complete_pointer_reads_keep_their_stores_across_sibling_writes() {
    let _session = crate::kernel::VerificationSession::enter();
    let flag = slot();
    let object = flag.offset_by_bytes(8);
    let callback = flag.offset_by_bytes(16);
    let sibling = flag.offset_by_bytes(24);
    let target = OldAddress::symbolic(Variable(38_143));
    let pointer = OldPointer::new(target.clone(), ProgramType::Int32Pointer)
        .with_bounds(Some(SubobjectBounds::constant(target, 4)));
    let function = OldPointer::new(
        OldAddress::function("callback_target"),
        ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    );
    let start =
        ExecutionState::new().with_memory(SymbolicMemory::new().with_block(flag.base.clone(), 28));
    let written = start.clone().with_memory(
        start
            .memory()
            .clone()
            .store(flag.clone(), ProgramValue::bool_constant(true))
            .store(object.clone(), ProgramValue::Pointer(pointer.clone()))
            .store(callback.clone(), ProgramValue::Pointer(function.clone())),
    );
    let mut samples = Vec::new();
    for count in [4, 64, 1024] {
        let mut state = written.clone();
        for value in 0..count {
            state = state.clone().with_memory(state.memory().clone().store(
                sibling.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(value)),
            ));
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let point = state.program_point();
            let flag_version = point
                .indexed_typed_version(&flag, ProgramType::Bool)
                .unwrap();
            assert_eq!(flag_version.read_version_id(), written.program_point_id());
            assert!(
                point
                    .indexed_integer_version(&flag, LoadKind::UInt8)
                    .is_none()
            );
            for (cell, stored) in [(&object, &pointer), (&callback, &function)] {
                let version = point
                    .indexed_typed_version(cell, stored.program_type())
                    .unwrap();
                let read = OldPointer::from_point_read(version, stored.program_type(), cell);
                assert_eq!(
                    read.address()
                        .as_loaded_value()
                        .unwrap()
                        .point
                        .read_version_id(),
                    written.program_point_id()
                );
                assert_eq!(
                    crate::kernel::eval::pointer_read_over_write_program_value(read.address())
                        .as_ref(),
                    Some(stored)
                );
            }
        });
        samples.push((count, work));
    }
    assert!(
        samples.iter().all(|&(_, work)| work <= samples[0].1 + 8),
        "{samples:?}"
    );
    let partial = written.clone().with_memory(written.memory().clone().store(
        object.offset_by_bytes(4),
        ProgramValue::UInt8(OldMachineTerm::narrow_constant(
            MachineIntegerType::UInt8,
            0,
        )),
    ));
    assert!(
        partial
            .program_point()
            .indexed_typed_version(&object, ProgramType::Int32Pointer)
            .is_none()
    );
}

#[test]
fn opaque_integer_call_outputs_follow_checked_local_effects() {
    for ty in [
        ProgramType::Int32,
        ProgramType::UInt32,
        ProgramType::Int8,
        ProgramType::UInt8,
        ProgramType::Int16,
        ProgramType::UInt16,
        ProgramType::Int64,
        ProgramType::UInt64,
        ProgramType::Int128,
        ProgramType::UInt128,
    ] {
        assert_opaque_integer_call_output(ty);
    }
}

fn assert_opaque_integer_call_output(ty: ProgramType) {
    let _session = crate::kernel::VerificationSession::enter();
    let output = slot();
    let sibling = SymbolicMemory::local_pointer("disjoint");
    let width = ty.byte_width();
    let output_range =
        MemoryRange::new_with_element_width(output.clone(), 0.into(), 1.into(), width);
    let sibling_range = MemoryRange::new(sibling.clone(), 0.into(), 1.into());
    let entry = ExecutionState::new().begin_function_entry_memory();
    let start = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_declared_scalar_block(output.base.clone(), width, ty)
            .with_block(sibling.base.clone(), 4),
    );
    let call = |state: &ExecutionState, index, range: &MemoryRange| {
        state
            .clone()
            .with_memory(state.memory().clone().with_call_memory_havoc(
                Variable(index),
                std::slice::from_ref(range),
                &PureFactContext::new(),
                None,
            ))
    };
    let output_return = |mut state: ExecutionState| {
        state.set_memory_directly(
            state
                .memory()
                .clone()
                .with_initialized_call_output(&output, width),
        );
        state
    };
    let returned = output_return(call(&start, 38_201, &output_range));
    let select = |state: &ExecutionState| state.program_point().ordinary_typed_version(&output, ty);
    let version = select(&returned).unwrap_or_else(|| panic!("opaque {ty:?} output has a version"));
    assert_eq!(version.read_version_id(), returned.program_point_id());
    assert_eq!(
        returned
            .program_point()
            .indexed_array_version(&AddressBase::ExternalArgument)
            .and_then(|version| version.read_version_id()),
        entry.program_point_id(),
        "an initialized local call output preserves the caller array version"
    );
    assert!(version.indexed_integer_store_bits().is_none());
    assert!(returned.memory().known_value(&output).is_none());
    // The output identifies one integer cell, even when another type uses
    // the same load-kind carrier.
    for unrelated_type in [
        ProgramType::Bool,
        ProgramType::Int32Pointer,
        ProgramType::Float64,
    ] {
        assert!(
            returned
                .program_point()
                .ordinary_typed_version(&output, unrelated_type)
                .is_none(),
            "{ty:?} output cannot name a {unrelated_type:?} read"
        );
    }
    assert!(
        returned
            .memory()
            .has_initialized_bytes_under(&output, width, &PureFactContext::new())
    );

    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut state = returned.clone();
        for i in 0..size {
            state = call(&state, 39_000 + i, &sibling_range);
        }
        let (selected, work) =
            crate::instrumentation::measure_deterministic_work(|| select(&state));
        assert_eq!(selected, Some(version.clone()));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );

    let changed = call(&returned, 40_000, &output_range);
    assert!(select(&changed).is_none());
    let returned_again = output_return(changed);
    let new_version = select(&returned_again).expect("the new output has its own version");
    assert_eq!(
        new_version.read_version_id(),
        returned_again.program_point_id()
    );
    assert_ne!(new_version, version);
}

#[test]
fn fold_cell_instantiation_keeps_the_entry_point_across_disjoint_stores() {
    use crate::kernel::IntegerTerm;

    let _session = crate::kernel::VerificationSession::enter();
    let entry = ExecutionState::new().begin_function_entry_memory();
    let cell = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(4).into(),
    };
    let local = slot();
    let declared = entry
        .clone()
        .with_memory(entry.memory().clone().with_block(local.base.clone(), 4));
    let accumulator = Variable(38_231);
    let item = Variable(38_232);
    let symbolic_cell = OldAddress {
        offset: OldAddressOffset::scale_int32(OldMachineTerm::Variable(item), 4).into(),
        ..cell.clone()
    };
    let read = |source: &ProgramPoint, address: &OldAddress| {
        let point = source
            .entry_integer_version(address, LoadKind::Int32)
            .unwrap();
        OldMachineTerm::read_named(point, Box::new(address.clone()), LoadKind::Int32)
    };
    let observation = |term| IntegerTerm::from_machine(MachineIntegerType::Int32, term).unwrap();
    let expected = read(&entry.program_point(), &cell);
    let expected_integer = observation(expected.clone());
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut state = declared.clone();
        for value in 0..count {
            state = state.clone().with_memory(state.memory().clone().store(
                local.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(value)),
            ));
        }
        let body = read(&state.program_point(), &symbolic_cell);
        let integer_body = observation(body.clone());
        let ((native, integer), work) = crate::instrumentation::measure_deterministic_work(|| {
            let zero = OldMachineTerm::constant(0);
            let one = OldMachineTerm::constant(1);
            let native = crate::kernel::reasoning::order_reasoning::instantiate_range_fold_step(
                &body,
                accumulator,
                &zero,
                item,
                &one,
            );
            let integer = crate::kernel::reasoning::instantiate_integer_range_fold_step(
                &integer_body,
                accumulator,
                &IntegerTerm::constant_i64(0),
                item,
                &IntegerTerm::constant_i64(1),
                Some(MachineIntegerType::Int32),
            )
            .unwrap();
            (native, integer)
        });
        assert_eq!(native, expected);
        assert_eq!(integer, expected_integer);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] + 8),
        "{samples:?}"
    );
}

#[test]
fn generic_entry_cells_and_compact_runs_keep_the_same_version_across_local_stores() {
    let _session = crate::kernel::VerificationSession::enter();
    let parameter = crate::kernel::TypeParameterName::intern("PointNamedCell");
    let ty = ProgramType::Parameter(parameter);
    let base = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0).into(),
    };
    let cell = base.offset_by_bytes(ty.byte_width());
    let entry = ExecutionState::new().begin_function_entry_memory();
    let source = entry.program_point();
    let expected =
        crate::kernel::AlgebraicTermNode::parameter_cell_load(&source, cell.clone(), parameter);
    let ProgramValue::Parameter(expected_term) = &expected else {
        panic!("generic cell has its abstract type");
    };
    let crate::kernel::AlgebraicTermNode::MemoryLoad { point, .. } = &expected_term.node else {
        panic!("generic cell has its own read");
    };
    assert_eq!(point.read_version_id(), source.id());

    let local = slot();
    let declared = entry
        .clone()
        .with_memory(entry.memory().clone().with_block(local.base.clone(), 4));
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut state = declared.clone();
        for value in 0..count {
            state = state.clone().with_memory(state.memory().clone().store(
                local.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(value)),
            ));
        }
        let source = state.program_point();
        let run = crate::kernel::CellRun::new_at(
            base.clone(),
            ty.byte_width(),
            ty,
            count,
            source.clone(),
            crate::kernel::RunValueMode::Load,
            crate::kernel::IndexIntervals::default(),
        );
        let ((named, compact), work) = crate::instrumentation::measure_deterministic_work(|| {
            let named = crate::kernel::AlgebraicTermNode::parameter_cell_load(
                &source,
                cell.clone(),
                parameter,
            );
            (named, run.value(1))
        });
        assert_eq!(named, expected);
        assert_eq!(compact, expected);
        samples.push(work);
    }
    assert_eq!(samples, vec![samples[0]; samples.len()]);

    let other_entry = ExecutionState::new().begin_function_entry_memory();
    assert_ne!(
        crate::kernel::AlgebraicTermNode::parameter_cell_load(
            &other_entry.program_point(),
            cell.clone(),
            parameter,
        ),
        expected,
    );
    let changed = entry
        .clone()
        .with_memory(entry.memory().clone().store(cell.clone(), expected.clone()));
    assert!(
        changed
            .program_point()
            .generic_entry_version(&cell, parameter)
            .is_none()
    );
}

#[test]
fn a_static_scalar_entry_version_ignores_disjoint_writes_in_its_block() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = SymbolicMemory::global_pointer("static_read");
    let entry = ExecutionState::new().begin_function_entry_memory();
    let entry = entry
        .clone()
        .with_function_entry_memory(entry.memory().clone().with_block(cell.base.clone(), 4100));
    let store = |state: &ExecutionState, address, bits| {
        state.clone().with_memory(
            state
                .memory()
                .clone()
                .store(address, ProgramValue::Int32(OldMachineTerm::constant(bits))),
        )
    };
    let mut samples = Vec::new();
    for count in [4, 64, 1024] {
        let mut state = entry.clone();
        for index in 1..=count {
            state = store(&state, cell.offset_by_bytes(4 * index), index);
        }
        let point = state.program_point();
        let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
            point.unwritten_static_scalar_version(&cell, ProgramType::Int32)
        });
        assert_eq!(
            version.and_then(|point| point.read_version_id()),
            entry.program_point_id(),
        );
        assert!(
            store(&state, cell.clone(), 0)
                .program_point()
                .unwritten_static_scalar_version(&cell, ProgramType::Int32)
                .is_none()
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn a_static_scalar_entry_version_ignores_disjoint_call_ranges_in_its_block() {
    use crate::kernel::{ExecutionBudget, ExpressionOutcome, ProgramExpression};

    let _session = crate::kernel::VerificationSession::enter();
    let cell = SymbolicMemory::global_pointer("static_call_read");
    let entry = ExecutionState::new().begin_function_entry_memory();
    let entry = entry
        .clone()
        .with_function_entry_memory(entry.memory().clone().with_block(cell.base.clone(), 8));
    let facts = PureFactContext::new();
    let range = |address| MemoryRange::new(address, 0u32.into(), 1u32.into());
    let sibling = range(cell.offset_by_bytes(4));
    let overlap = range(cell.clone());
    let call = |state: &ExecutionState, id, writes: &MemoryRange| {
        state
            .clone()
            .with_memory(state.memory().clone().with_storage_memory_havoc(
                Variable(id),
                std::slice::from_ref(writes),
                &facts,
            ))
    };
    let selected = |state: &ExecutionState| {
        state
            .program_point()
            .unwritten_static_scalar_version(&cell, ProgramType::Int32)
    };
    let read = ProgramExpression::Load(Box::new(ProgramExpression::Value(
        ProgramValue::typed_pointer(cell.clone(), ProgramType::Int32Pointer),
    )));
    let mut samples = Vec::new();
    for count in [4, 64, 256] {
        let mut state = entry.clone();
        for index in 0..count {
            state = call(&state, 91_000 + index, &sibling);
        }
        let (version, work) =
            crate::instrumentation::measure_deterministic_work(|| selected(&state));
        assert_eq!(
            version.and_then(|point| point.read_version_id()),
            entry.program_point_id()
        );
        let changed = call(&state, 92_000, &overlap);
        assert!(selected(&changed).is_none());
        assert!(selected(&call(&changed, 92_001, &sibling)).is_none());
        samples.push(work);

        let state = state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::view_memory(MemoryRange::access(cell.clone(), ProgramType::Int32)),
        ));
        let paths = crate::kernel::eval::evaluate_expression_value_paths(
            &state,
            &read,
            &facts,
            &mut ExecutionBudget::new(),
        )
        .expect("checked C read");
        let [path] = paths.as_slice() else {
            panic!("expected one read path");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("expected a symbolic int32 value");
        };
        let value = value.native();
        let ProgramValue::Int32(OldMachineTerm::MemoryLoad(point, address, LoadKind::Int32)) =
            value.as_ref()
        else {
            panic!("expected a typed int32 load");
        };
        assert_eq!(**address, cell);
        assert_eq!(point.read_version_id(), entry.program_point_id());
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );
}

/// A caller cell no write reached keeps its entry version across writes to
/// other cells of the same parameter origin. Selecting it costs a lookup
/// per byte of the read, not a walk over the writes before it.
#[test]
fn an_unwritten_parameter_cell_keeps_its_entry_version_across_sibling_writes() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = OldAddress {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0).into(),
    };
    let entry = ExecutionState::new().begin_function_entry_memory();
    let store = |state: &ExecutionState, address: OldAddress, bits| {
        state.clone().with_memory(
            state
                .memory()
                .clone()
                .store(address, ProgramValue::Int32(OldMachineTerm::constant(bits))),
        )
    };
    let read = |state: &ExecutionState, address: &OldAddress| {
        state
            .program_point()
            .entry_integer_version(address, LoadKind::Int32)
    };
    let at_entry = read(&store(&entry, cell.offset_by_bytes(4), 0), &cell)
        .expect("an entry version after one sibling write");
    assert_eq!(at_entry.read_version_id(), entry.program_point_id());
    let mut samples = Vec::new();
    for count in [4, 64, 1024] {
        let mut state = entry.clone();
        for index in 1..=count {
            state = store(&state, cell.offset_by_bytes(4 * index), index);
        }
        let point = state.program_point();
        let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
            point.entry_integer_version(&cell, LoadKind::Int32)
        });
        // The same read term as one taken before the other writes.
        assert_eq!(version.as_ref(), Some(&at_entry), "at {count} writes");
        samples.push(work);

        // A write reaching any byte of the cell ends its entry version.
        assert!(read(&store(&state, cell.offset_by_bytes(2), 0), &cell).is_none());
        assert!(read(&store(&state, cell.clone(), 0), &cell).is_none());
        // A write from another parameter origin may alias the cell.
        let other_origin = OldAddress {
            base: AddressBase::ExternalArgument,
            offset: OldAddressOffset::Variable(Variable(38_901)).into(),
        };
        assert!(read(&store(&state, other_origin, 0), &cell).is_none());
        // A write through a pointer of unknown storage may too.
        assert!(
            read(
                &store(&state, OldAddress::symbolic(Variable(38_902)), 0),
                &cell
            )
            .is_none()
        );
        // A local store leaves caller storage alone.
        let local = SymbolicMemory::local_pointer("unwritten_parameter_local");
        let with_local = state
            .clone()
            .with_memory(state.memory().clone().with_block(local.base.clone(), 4));
        assert_eq!(
            read(&store(&with_local, local, 0), &cell).as_ref(),
            Some(&at_entry)
        );
    }
    assert!(
        samples.iter().all(|&work| work == samples[0]),
        "{samples:?}"
    );
}
