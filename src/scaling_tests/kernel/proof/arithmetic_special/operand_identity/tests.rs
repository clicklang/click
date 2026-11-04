use super::*;
use crate::kernel::{
    IntegerTerm, KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm, Variable,
};

#[test]
fn certificate_identity_bounds_shared_prefix_work_without_export() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(997131));
        let right =
            IntegerTerm::from_machine(format, MachineTerm::Variable(Variable(997132))).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for depth in 1..=size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let operand = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let condition = ConditionTerm::integer_less_equal(
                    IntegerTerm::Machine(operand.clone()),
                    right.clone(),
                );
                assert_eq!(condition_equal(&condition, &condition), depth <= 7);
                assert!(!operand.has_boxed_operand());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
