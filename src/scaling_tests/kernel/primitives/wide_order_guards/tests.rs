use super::*;
use crate::kernel::{
    IntegerTerm, KernelTerm, KernelTermExport, KernelType, SharedMachineIntegerTerm, Variable,
};

#[test]
fn wide_guards_retain_growing_shared_prefixes_without_export() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::C(T::UInt64.c_type()), Variable(998171));
        let removed = KernelTerm::variable(KernelType::C(T::UInt64.c_type()), Variable(998172));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    T::UInt64,
                    Op::Add,
                    [root.clone(), root.clone()],
                );
                let difference = KernelTerm::machine_binary_shared(
                    T::UInt64,
                    Op::Subtract,
                    [root.clone(), removed.clone()],
                );
                let root_operand =
                    SharedMachineIntegerTerm::from_shared(T::UInt64, root.clone()).unwrap();
                let difference_operand =
                    SharedMachineIntegerTerm::from_shared(T::UInt64, difference).unwrap();
                let query = C::integer_less_equal(
                    IntegerTerm::Machine(difference_operand.clone()),
                    IntegerTerm::Machine(root_operand.clone()),
                );
                let guard = query.uint64_subtraction_guard().unwrap();
                let view = comparison_view(&guard, true).unwrap();
                assert!(same(view.operands[1].operand_view(), V::Shared(&root)));
                assert!(
                    !root_operand.has_boxed_operand() && !difference_operand.has_boxed_operand()
                );
                assert!(query.uint64_successor_guard().is_none());
                assert!(query.uint64_remainder_bound_guard().is_none());
                assert!(query.uint64_subtraction_upper_bound_guards().is_none());
                assert!(
                    query
                        .uint64_partial_restoration_upper_bound_guards()
                        .is_none()
                );
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
