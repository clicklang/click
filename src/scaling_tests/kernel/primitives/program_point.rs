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
