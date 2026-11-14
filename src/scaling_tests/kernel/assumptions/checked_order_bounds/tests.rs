use super::*;
use crate::kernel::{
    IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, ProgramType, SharedMachineIntegerTerm,
};

#[test]
fn signed_wide_shared_prefix_bounds_do_not_materialize_operands() {
    let mut samples = Vec::new();
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let mut term =
            KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(982001));
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
                index.adjust(&condition, true);
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
            let mut term =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(982002));
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
                    index.adjust(&condition, true);
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

#[test]
fn native_order_premises_select_retained_promoted_call_bounds() {
    use crate::kernel::{KernelTermExport, PureFunctionArgument};
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
    ] {
        for truth in [false, true] {
            let _session = crate::kernel::VerificationSession::enter();
            let call = MachineTerm::ClickFunctionApplication {
                name: "indexed_digit".into(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::UInt64(
                    MachineTerm::uint64_constant(7),
                ))],
            };
            let endpoint =
                MachineTerm::machine_integer_cast(MachineIntegerType::UInt8, format, call);
            let literal = if format == MachineIntegerType::Int64 {
                MachineTerm::int64_constant(48)
            } else {
                MachineTerm::constant(48)
            };
            let fact = ConditionTerm::Compare {
                format,
                relation: CompareRelation::LessEqual,
                left: Box::new(literal),
                right: Box::new(endpoint.clone()),
            };
            let mut index = CheckedOrderBounds::default();
            index.adjust(&fact, truth);
            let root = KernelTerm::retained_native_machine_operand(format, &endpoint);
            let exports = KernelTermExport::machine_export_count();
            let native = if format == MachineIntegerType::Int64 {
                index.signed_wide_interval(&endpoint)
            } else {
                index.interval(&endpoint, format == MachineIntegerType::UInt32)
            };
            let shared = if format == MachineIntegerType::Int64 {
                index.signed_wide_interval_view(MachineOperandView::Shared(&root))
            } else {
                index.interval_view(
                    MachineOperandView::Shared(&root),
                    format == MachineIntegerType::UInt32,
                )
            };
            assert!(native.is_some(), "{format:?}/{truth}");
            assert_eq!(native, shared, "{format:?}/{truth}");
            if truth {
                assert_eq!(shared.unwrap().0, 48);
            } else {
                assert_eq!(shared.unwrap().1, 47);
            }
            if format != MachineIntegerType::Int64 {
                assert_eq!(
                    index.interval_view(
                        MachineOperandView::Shared(&root),
                        format != MachineIntegerType::UInt32
                    ),
                    None
                );
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
