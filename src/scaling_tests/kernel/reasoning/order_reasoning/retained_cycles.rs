#[test]
fn growing_cycle_endpoints_keep_shared_identity() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(995311));
        let other = IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(995312))).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                assert!(
                    crate::kernel::reasoning::path_facts::conjunction_order_facts_are_inconsistent(
                        &cycle(observed(root.clone()), other.clone(), true, false)
                    )
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
