use super::*;
use crate::kernel::{
    IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, ProgramType, SharedMachineIntegerTerm,
    Variable,
};

#[test]
fn conversion_root_queries_retain_shared_prefixes() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut term =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(982100));
        let narrow = IntegerTerm::from_machine(
            MachineIntegerType::Int8,
            MachineTerm::Variable(Variable(982101)),
        )
        .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                term = KernelTerm::arithmetic_binary(
                    ty,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                )
                .unwrap();
                let observation = SharedMachineIntegerTerm::from_shared(ty, term.clone()).unwrap();
                let integer = IntegerTerm::Machine(observation.clone());
                assert!(cast_operands(&integer).is_empty());
                assert!(!narrow_widening(&integer, &narrow));
                assert_eq!(
                    widened_narrow_word(&integer).unwrap().retain(ty).id(),
                    observation.id()
                );
                assert!(!observation.has_boxed_operand());
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

#[test]
fn cast_rule_keeps_shared_operand_prefixes() {
    for (source, destination, accepted) in [
        (MachineIntegerType::Int32, MachineIntegerType::UInt32, true),
        (MachineIntegerType::UInt64, MachineIntegerType::Int64, true),
        (MachineIntegerType::Int64, MachineIntegerType::UInt64, false),
        (MachineIntegerType::Int32, MachineIntegerType::Int8, true),
    ] {
        let mut samples = Vec::new();
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut term =
                KernelTerm::variable(KernelType::Program(source.c_type()), Variable(982107));
            let opaque = IntegerTerm::from_machine(
                source,
                MachineTerm::PureFunctionApplication {
                    name: "cast_opaque_word".to_string(),
                    arguments: vec![MachineTerm::Variable(Variable(982108))],
                },
            )
            .unwrap();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        source,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let operand =
                        SharedMachineIntegerTerm::from_shared(source, term.clone()).unwrap();
                    let observed = SharedMachineIntegerTerm::from_shared(
                        destination,
                        term.with_machine_observation_type(destination),
                    )
                    .unwrap();
                    assert_eq!(
                        cast(
                            &IntegerTerm::Machine(observed.clone()),
                            &IntegerTerm::Machine(operand.clone())
                        )
                        .is_some(),
                        accepted
                    );
                    assert!(cast(&IntegerTerm::Machine(observed.clone()), &opaque).is_none());
                    assert!(!operand.has_boxed_operand());
                    assert!(!observed.has_boxed_operand());
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
}
