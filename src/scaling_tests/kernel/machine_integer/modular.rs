#[test]
fn residue_projection_reuses_cold_shared_dags_without_export() {
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let source = shared(MachineIntegerType::Int32, depth);
        let condition =
            ConditionTerm::IntegerEqual(source.into(), IntegerTerm::constant_i64(0).into());
        let before = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            wrapped_equality_at(MachineIntegerType::UInt32, &condition, true)
        });
        assert!(result.is_some());
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
