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
