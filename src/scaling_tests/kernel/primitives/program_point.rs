use super::*;

#[test]
fn external_displacements_and_heap_indexes_use_only_their_selected_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let parameter = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(38_151)),
    };
    let other_parameter = Address {
        offset: AddressOffset::Variable(Variable(38_152)),
        ..parameter.clone()
    };
    let heap = Address {
        base: AddressBase::Heap(38_153),
        offset: AddressOffset::Constant(0),
    };
    let start =
        ExecutionState::new().with_memory(SymbolicMemory::new().with_block(heap.base.clone(), 8));
    let store = |state: &ExecutionState, address: &Address, bits| {
        state.clone().with_memory(state.memory().clone().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(bits)),
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

    let symbolic_heap = Address {
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
fn pending_successor_lookup_ignores_recorded_log_length() {
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let mut memory = start.memory().clone();
        for _ in 0..count {
            memory = memory
                .store(slot(), ProgramValue::Int32(MachineTerm::constant(1)))
                .store(slot(), ProgramValue::Int32(MachineTerm::constant(0)));
        }
        let moved = start.clone().with_materialized_memory(memory);
        assert_eq!(moved.memory(), start.memory());
        let (point, cold) =
            crate::instrumentation::measure_deterministic_work(|| moved.program_point());
        let (again, warm) =
            crate::instrumentation::measure_deterministic_work(|| moved.program_point());
        assert_ne!(point.id(), start.program_point().id());
        assert_eq!(point.id(), again.id());
        samples.push((count, cold, warm));
    }
    assert!(
        samples
            .iter()
            .all(|(_, cold, warm)| (*cold, *warm) == (samples[0].1, samples[0].2)),
        "{samples:?}"
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
                ProgramValue::Int32(MachineTerm::constant(index)),
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
            Some(&MachineTerm::constant(1))
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
                ProgramValue::Int32(MachineTerm::constant(index)),
            );
        }
        let mut current = start.with_memory(memory);
        let original = current.program_point_id();
        let changed = slot.offset_by_bytes(4 * count);
        for _ in 0..8 {
            let write = |value| {
                current.clone().with_memory(current.memory().clone().store(
                    changed.clone(),
                    ProgramValue::Int32(MachineTerm::constant(value)),
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
        let target = Address {
            base: "local:target".into(),
            offset: AddressOffset::Constant(0),
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
                ProgramValue::Int32(MachineTerm::constant(index)),
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
    let cell = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(38_154)),
    };
    let target = Address::symbolic(Variable(38_155));
    let stored = Pointer::new(target.clone(), ProgramType::Int32Pointer)
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
                ProgramValue::Int32(MachineTerm::constant(bits)),
            ));
        }
        let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
            state
                .program_point()
                .indexed_typed_version(&cell, stored.program_type())
                .expect("complete pointer store at the parameter cell")
        });
        assert_eq!(version.read_version_id(), written.program_point_id());
        let read = Pointer::from_point_read(version, stored.program_type(), &cell);
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
        ProgramValue::Int32(MachineTerm::constant(0)),
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
    let target = Address::symbolic(Variable(38_143));
    let pointer = Pointer::new(target.clone(), ProgramType::Int32Pointer)
        .with_bounds(Some(SubobjectBounds::constant(target, 4)));
    let function = Pointer::new(
        Address::function("callback_target"),
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
                ProgramValue::Int32(MachineTerm::constant(value)),
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
                let read = Pointer::from_point_read(version, stored.program_type(), cell);
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
        ProgramValue::UInt8(MachineTerm::narrow_constant(MachineIntegerType::UInt8, 0)),
    ));
    assert!(
        partial
            .program_point()
            .indexed_typed_version(&object, ProgramType::Int32Pointer)
            .is_none()
    );
}

#[test]
fn opaque_call_word_versions_follow_checked_local_effects() {
    for ty in [ProgramType::Int32, ProgramType::UInt32] {
        assert_opaque_call_word_versions(ty);
    }
}

fn assert_opaque_call_word_versions(ty: ProgramType) {
    let _session = crate::kernel::VerificationSession::enter();
    let output = slot();
    let sibling = SymbolicMemory::local_pointer("disjoint");
    let output_range = MemoryRange::new(output.clone(), 0.into(), 1.into());
    let sibling_range = MemoryRange::new(sibling.clone(), 0.into(), 1.into());
    let start = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_declared_scalar_block(output.base.clone(), 4, ty)
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
        state.set_memory_directly(state.memory().clone().with_initialized_call_word(&output));
        state
    };
    let returned = output_return(call(&start, 38_201, &output_range));
    let select = |state: &ExecutionState| {
        state
            .program_point()
            .ordinary_typed_version(&output, ty)
    };
    let version = select(&returned).expect("opaque output has a version");
    assert_eq!(version.read_version_id(), returned.program_point_id());
    assert!(version.indexed_integer_store_bits().is_none());
    assert!(returned.memory().known_value(&output).is_none());
    assert!(
        returned
            .memory()
            .has_initialized_bytes_under(&output, 4, &PureFactContext::new())
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
    let cell = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(4),
    };
    let local = slot();
    let declared = entry
        .clone()
        .with_memory(entry.memory().clone().with_block(local.base.clone(), 4));
    let accumulator = Variable(38_231);
    let item = Variable(38_232);
    let symbolic_cell = Address {
        offset: AddressOffset::scale_int32(MachineTerm::Variable(item), 4),
        ..cell.clone()
    };
    let read = |source: &ProgramPoint, address: &Address| {
        let point = source
            .entry_integer_version(address, LoadKind::Int32)
            .unwrap();
        MachineTerm::MemoryLoad(point, Box::new(address.clone()), LoadKind::Int32)
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
                ProgramValue::Int32(MachineTerm::constant(value)),
            ));
        }
        let body = read(&state.program_point(), &symbolic_cell);
        let integer_body = observation(body.clone());
        let ((native, integer), work) = crate::instrumentation::measure_deterministic_work(|| {
            let zero = MachineTerm::constant(0);
            let one = MachineTerm::constant(1);
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
    let base = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Constant(0),
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
                ProgramValue::Int32(MachineTerm::constant(value)),
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
