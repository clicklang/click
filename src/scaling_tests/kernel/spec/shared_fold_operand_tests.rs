#[test]
fn conservative_carrier_queries_do_not_rewalk_growing_prefixes() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(CType::Int32), Variable(998100));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(KernelType::C(CType::Int32), Variable(998101 + index)),
                    ],
                );
                let term = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                );
                assert!(integer_carrier_in_integer(&term, Variable(998999)));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
