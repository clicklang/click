use super::*;

#[test]
fn cross_width_observation_registration_keeps_shared_prefixes() {
    use crate::kernel::{KernelType, MachineBinaryOp};
    let mut measurements = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let mut root =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982402));
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
        let mut root =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982414));
        let right =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982415));
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

#[test]
fn shared_cast_registration_and_readings_reuse_growing_prefixes() {
    use crate::kernel::{KernelType, MachineCastSpelling as E, MachineOperandView};
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::Program(MachineIntegerType::Int32.program_type()),
            Variable(985201),
        );
        let mut classes = TermClasses::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let wide = KernelTerm::machine_cast_shared(
                    E::Generic,
                    MachineIntegerType::Int32,
                    MachineIntegerType::Int64,
                    root.clone(),
                );
                let observed = MachineOperandView::Shared(&wide)
                    .observe(MachineIntegerType::Int64)
                    .unwrap();
                let IntegerTerm::Machine(machine) = &observed else {
                    panic!("observation");
                };
                let read = observed.value_read();
                assert!(
                    matches!(read, IntegerTerm::Machine(value) if value.ty() == MachineIntegerType::Int32)
                );
                classes.intern_integer(&observed);
                assert!(!machine.has_boxed_operand());
                root = KernelTerm::machine_cast_shared(
                    E::Generic,
                    MachineIntegerType::Int64,
                    MachineIntegerType::Int32,
                    wide,
                );
                let narrowed = MachineOperandView::Shared(&root)
                    .observe(MachineIntegerType::Int32)
                    .unwrap();
                classes.intern_integer(&narrowed);
                let IntegerTerm::Machine(machine) = &narrowed else {
                    panic!("observation");
                };
                assert!(!machine.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}
