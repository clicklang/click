#[test]
fn preparing_contract_inputs_keeps_growing_return_operands_shared() {
    let mut previous = None;
    for depth in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996810));
        let mut root = atom.clone();
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let input = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let exports = KernelTermExport::machine_export_count();
        let (actual, work) =
            crate::instrumentation::measure_deterministic_work(|| prepared_input(input));
        assert_eq!(actual.shared(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "contract input preparation must not walk the result"
            );
        }
        previous = Some(work);
    }
}
