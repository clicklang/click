use super::*;

#[test]
fn closed_conditional_atom_reads_fixed_roots_without_exporting_arithmetic() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, ProgramType};
    let mut baseline = None;
    for size in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let literal = |n| {
            KernelTerm::retained_native_machine_operand(format, &MachineTerm::uint64_constant(n))
        };
        let guard =
            KernelTerm::boolean_comparison_raw(format, R::LessThan, [literal(9), literal(8)]);
        let variable =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(999740));
        let mut arithmetic = variable.clone();
        for _ in 0..size {
            arithmetic = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [arithmetic, literal(1)],
            );
        }
        let hit = KernelTerm::machine_if_shared(format, [guard.clone(), variable, literal(3)]);
        let miss = KernelTerm::machine_if_shared(format, [guard, arithmetic, literal(3)]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(matches!(
                closed_order_conditional_atom(&hit),
                Some(MachineTerm::If { .. })
            ));
            assert!(closed_order_conditional_atom(&miss).is_none());
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "{size} arithmetic nodes"
        );
    }
}
