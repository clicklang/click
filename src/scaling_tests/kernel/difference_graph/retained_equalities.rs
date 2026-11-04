#[test]
fn retained_equality_aliases_reuse_one_coordinate_across_growing_prefixes() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineOperandView as V};
    for format in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt64,
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(993251));
            let y = MachineTerm::Variable(Variable(993252));
            let mut facts = DifferenceGraph::new();
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for step in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Multiply,
                        [root.clone(), root.clone()],
                    );
                    let alias = condition_for_operand_views(
                        format,
                        CompareRelation::Equal,
                        [V::Shared(&root), V::Legacy(&y)],
                    );
                    assert_eq!(facts.decide(&alias), None);
                    facts.assume_condition(&alias, true);
                    assert_eq!(facts.decide(&alias), Some(true), "{format:?} {size} step {step}");
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            assert!(pair[1].1 <= pair[0].1 * 5, "{format:?}: {samples:?}");
        }
    }
}
