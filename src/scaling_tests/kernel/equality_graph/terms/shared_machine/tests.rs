use super::*;

#[test]
fn cross_width_observation_registration_keeps_shared_prefixes() {
    use crate::kernel::{KernelType, MachineBinaryOp};
    let mut measurements = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982402));
        let mut classes = TermClasses::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::arithmetic_binary(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                )
                .unwrap();
                let observed = MachineIntegerType::Int32;
                let operand = SharedMachineIntegerTerm::from_shared(
                    observed,
                    root.with_machine_observation_type(observed),
                )
                .unwrap();
                let observation = IntegerTerm::Machine(operand.clone());
                let first = classes.intern_integer(&observation);
                let second = classes.intern_integer(&observation);
                assert_eq!(classes.root(first), classes.root(second));
                assert!(!operand.has_boxed_operand());
            }
        });
        measurements.push((size, work));
    }
    for pair in measurements.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{measurements:?}");
    }
}

#[test]
fn comparison_nodes_reuse_shared_prefixes() {
    use crate::kernel::{CompareRelation, KernelType, MachineBinaryOp, MachineOperandView};
    let mut measurements = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982414));
        let right = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982415));
        let mut classes = TermClasses::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::arithmetic_binary(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                )
                .unwrap();
                let observation =
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let operands = [
                    observation.operand_view(),
                    MachineOperandView::Shared(&right),
                ];
                let first = classes
                    .machine_comparison_node(format, CompareRelation::LessEqual, operands)
                    .unwrap();
                let second = classes
                    .machine_comparison_node(format, CompareRelation::LessEqual, operands)
                    .unwrap();
                assert_eq!(classes.root(first), classes.root(second));
                assert!(!classes.knows_machine_comparison(
                    format,
                    CompareRelation::LessEqual,
                    operands,
                    true
                ));
                assert!(classes.admit_machine_comparison(
                    format,
                    CompareRelation::LessEqual,
                    operands,
                    true
                ));
                assert!(classes.knows_machine_comparison(
                    format,
                    CompareRelation::LessEqual,
                    operands,
                    true
                ));
                assert!(!classes.knows_machine_comparison(
                    format,
                    CompareRelation::LessEqual,
                    operands,
                    false
                ));
                assert!(!observation.has_boxed_operand());
            }
        });
        measurements.push((size, work));
    }
    for pair in measurements.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{measurements:?}");
    }
}
