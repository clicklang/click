use super::*;
use crate::kernel::{KernelFoldIndex, KernelTerm, MachineBinaryOp};

#[test]
fn common_fold_alpha_keys_scale_with_selected_shared_bodies_without_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let fold = |acc| {
            let mut body = KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Legacy(&MachineTerm::Variable(Variable(acc))),
            );
            for _ in 0..size {
                body = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [body.clone(), body],
                );
            }
            let zero = KernelTerm::retained_machine_operand(
                MachineIntegerType::Int32,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
            );
            KernelFold::new(
                KernelFoldIndex::Int32,
                Variable(acc),
                Variable(acc + 1),
                [zero.clone(), zero.clone(), zero, body],
            )
            .unwrap()
        };
        let a = fold(110);
        let b = fold(120);
        let exports = KernelTermExport::machine_export_count();
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| alpha_equivalent(&a, &b));
        assert_eq!(result, Some(true));
        assert!(work <= 100 * size + 200, "size={size}, work={work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
