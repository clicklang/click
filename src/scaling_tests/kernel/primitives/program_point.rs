use super::*;

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
                        .indexed_local_integer_version(&first, LoadKind::Int32)
                        .unwrap(),
                    point
                        .indexed_local_integer_version(&second, LoadKind::Int32)
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
                    .indexed_local_integer_version(&slot, LoadKind::Int32)
                    .and_then(|point| point.read_version_id()),
                original
            );
            assert!(
                joined
                    .program_point()
                    .indexed_local_integer_version(&changed, LoadKind::Int32)
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
            .with_loop_memory_havoc_preserving_loans(
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
                        .indexed_local_integer_version(&slot, LoadKind::Int32)
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
