use super::*;
use crate::kernel::{
    CType, IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm,
};

#[test]
fn signed_wide_shared_prefix_bounds_do_not_materialize_operands() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let mut term = KernelTerm::variable(KernelType::C(CType::Int64), Variable(982001));
        let mut index = CheckedOrderBounds::default();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                term = KernelTerm::arithmetic_binary(
                    format,
                    MachineBinaryOp::Add,
                    [term.clone(), term.clone()],
                )
                .unwrap();
                let observation =
                    SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                let condition = ConditionTerm::integer_less_equal(
                    IntegerTerm::Machine(observation.clone()),
                    IntegerTerm::constant(7.into()),
                );
                index.adjust(&condition, true, true);
                assert_eq!(
                    index.signed_wide_interval_view(observation.operand_view()),
                    Some((i64::MIN, 7))
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
fn shared_word_prefix_bounds_do_not_materialize_operands() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
        let mut samples = Vec::new();
        for size in [8, 32, 96] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut term = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982002));
            let mut index = CheckedOrderBounds::default();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let condition = ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(observation.clone()),
                        IntegerTerm::constant(7.into()),
                    );
                    index.adjust(&condition, true, true);
                    assert_eq!(
                        index.interval_view(
                            observation.operand_view(),
                            format == MachineIntegerType::UInt32
                        ),
                        Some((
                            if format == MachineIntegerType::Int32 {
                                i64::from(i32::MIN)
                            } else {
                                0
                            },
                            7
                        ))
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
}
