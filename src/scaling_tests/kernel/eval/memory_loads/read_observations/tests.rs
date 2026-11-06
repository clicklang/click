use super::*;

#[test]
fn selected_read_metadata_stays_indexed_as_observations_and_branches_grow() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let memory = intern_c_memory(CMemory::new());
        let address = Pointer::symbolic(Variable(998_703));
        let term = KernelTerm::scalar_read_descriptor(
            MachineIntegerType::Int32,
            &memory,
            &address,
            LoadKind::Int32,
        )
        .unwrap();
        let id = record(&memory, &address, LoadKind::Int32, &memory, 4);
        remember_term(&term, id);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                record(
                    &memory,
                    &address.offset_by_bytes(i * 8 + 8),
                    LoadKind::Int32,
                    &memory,
                    4,
                );
                let parent = capture();
                record(&memory, &address, LoadKind::Int32, &memory, 8);
                assert_eq!(
                    for_operand(MachineOperandView::Shared(&term))
                        .unwrap()
                        .bytes,
                    8
                );
                restore(&parent);
                assert_eq!(
                    for_operand(MachineOperandView::Shared(&term))
                        .unwrap()
                        .bytes,
                    4
                );
            }
        });
        assert_eq!(load_variable_registry_len(), 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
