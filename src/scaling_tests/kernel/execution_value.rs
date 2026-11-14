use super::*;

#[test]
fn retained_execution_handoffs_do_not_walk_the_value_dag() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let leaf = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998241));
        let mut root = leaf.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root, leaf.clone()],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut outcome = ExpressionOutcome::Value(ExecutionValue::from(root.clone()));
            for _ in 0..32 {
                outcome = outcome.map_value(|value| value.clone());
            }
            let ExpressionOutcome::Value(value) = outcome else {
                unreachable!()
            };
            assert_eq!(value.c_type(), ProgramType::UInt32);
            let (_, MachineOperandView::Shared(selected)) = value.machine().unwrap() else {
                panic!("shared operand")
            };
            assert_eq!(selected, &root);
            value
        });
        assert_eq!(value, ExecutionValue::Shared(root));
        assert_eq!(
            work, 0,
            "handoffs must not visit the selected DAG at size {size}"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
