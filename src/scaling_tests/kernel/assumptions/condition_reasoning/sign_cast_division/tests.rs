use super::*;
use crate::kernel::{CType, KernelTerm, KernelTermExport, KernelType, Variable};

#[test]
fn sign_division_construction_retains_growing_shared_operands() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut n = KernelTerm::variable(KernelType::C(CType::Int32), Variable(189121));
        let d = KernelTerm::variable(KernelType::C(CType::Int32), Variable(189122));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                n = KernelTerm::machine_binary_shared(Ty::Int32, Op::Add, [n.clone(), n.clone()]);
                let casted =
                    [&n, &d].map(|root| cast_operand(Ty::Int32, Ty::UInt32, View::Shared(root)));
                for op in [Op::Divide, Op::Remainder] {
                    let result = division_at_views(
                        Ty::UInt32,
                        op,
                        casted.each_ref().map(ComparisonOperand::operand_view),
                    );
                    assert_eq!(result.operand_view().binary().unwrap().1, op);
                }
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
