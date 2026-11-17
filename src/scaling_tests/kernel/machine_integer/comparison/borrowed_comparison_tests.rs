use super::*;

#[test]
fn conditional_atom_reads_fixed_roots_without_exporting_arithmetic() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};
    for format in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let literal = |n| {
                KernelTerm::retained_native_machine_operand(
                    format,
                    &if format == MachineIntegerType::UInt32 {
                        MachineTerm::uint32_constant(n as u32)
                    } else {
                        MachineTerm::uint64_constant(n)
                    },
                )
            };
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999740));
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [arithmetic, literal(1)],
                );
            }
            let guard_operands = [
                [literal(9), literal(8)],
                [variable.clone(), literal(8)],
                [literal(8), variable.clone()],
                [variable.clone(), variable.clone()],
                [arithmetic.clone(), literal(8)],
                [literal(8), arithmetic.clone()],
            ];
            let mut cases = guard_operands
                .into_iter()
                .enumerate()
                .flat_map(|(index, operands)| {
                    [R::LessThan, R::Equal]
                        .into_iter()
                        .map(move |relation| (index, operands.clone(), relation))
                })
                .map(|(index, operands, relation)| {
                    let guard_format =
                        if relation == R::Equal && format == MachineIntegerType::UInt64 {
                            MachineIntegerType::Int64
                        } else {
                            format
                        };
                    let guard =
                        KernelTerm::boolean_comparison_raw(guard_format, relation, operands);
                    let hit = KernelTerm::machine_if_shared(
                        format,
                        [guard.clone(), variable.clone(), literal(3)],
                    );
                    let miss = KernelTerm::machine_if_shared(
                        format,
                        [guard, arithmetic.clone(), literal(3)],
                    );
                    (hit, miss, index < 4)
                })
                .collect::<Vec<_>>();
            let flag = KernelTerm::variable(KernelType::Bool, Variable(999741));
            let mut compound = flag.clone();
            for index in 0..size {
                compound = KernelTerm::boolean_if([
                    flag.clone(),
                    compound,
                    KernelTerm::variable(KernelType::Bool, Variable(999742 + index)),
                ]);
            }
            for (guard, expected) in [(flag, true), (compound, false)] {
                let hit = KernelTerm::machine_if_shared(
                    format,
                    [guard.clone(), variable.clone(), literal(3)],
                );
                let miss =
                    KernelTerm::machine_if_shared(format, [guard, arithmetic.clone(), literal(3)]);
                cases.push((hit, miss, expected));
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (hit, miss, expected) in &cases {
                    assert_eq!(conditional_atom(hit).is_some(), *expected);
                    assert!(conditional_atom(miss).is_none());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{size} arithmetic nodes"
            );
        }
    }
}

#[test]
fn reflexive_variable_comparisons_do_not_walk_arithmetic_operands() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineOperandView as V,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999950));
            let one = KernelTerm::retained_native_machine_operand(
                format,
                &crate::kernel::machine_integer::range::constant_word(format, &1.into()).unwrap(),
            );
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [arithmetic, one.clone()],
                );
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let retained = logical_condition_for_operand_views(
                    format,
                    R::Equal,
                    [V::Shared(&variable), V::Shared(&variable)],
                );
                assert!(
                    matches!(retained, ConditionTerm::Compare { relation: R::Equal, left, right, .. }
                    if matches!((left.as_ref(), right.as_ref()), (MachineTerm::Variable(a), MachineTerm::Variable(b)) if a == b))
                );
                let other = logical_condition_for_operand_views(
                    format,
                    R::Equal,
                    [V::Shared(&arithmetic), V::Shared(&arithmetic)],
                );
                assert!(!matches!(other, ConditionTerm::Compare { .. }));
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{format:?}, {size} arithmetic nodes"
            );
        }
    }
}

#[test]
fn bitwise_conditional_arms_read_only_fixed_roots() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp as O};
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let mut baseline = None;
        for size in [16, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(999970));
            let literal = |n: u64| {
                KernelTerm::retained_native_machine_operand(
                    format,
                    &crate::kernel::machine_integer::range::constant_word(format, &n.into())
                        .unwrap(),
                )
            };
            let guard = KernelTerm::variable(KernelType::Bool, Variable(999971));
            let mut arithmetic = variable.clone();
            for _ in 0..size {
                arithmetic =
                    KernelTerm::machine_binary_shared(format, O::Add, [arithmetic, literal(1)]);
            }
            let cases = [O::BitwiseAnd, O::BitwiseOr, O::BitwiseXor].map(|op| {
                let bitwise = |a, b| KernelTerm::machine_binary_shared(format, op, [a, b]);
                let conditional =
                    |a, b| KernelTerm::machine_if_shared(format, [guard.clone(), a, b]);
                (
                    conditional(bitwise(variable.clone(), literal(7)), literal(3)),
                    conditional(literal(3), bitwise(literal(7), variable.clone())),
                    conditional(bitwise(arithmetic.clone(), literal(7)), literal(3)),
                    conditional(literal(3), bitwise(literal(7), arithmetic.clone())),
                )
            });
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (left, right, left_miss, right_miss) in &cases {
                    assert!(
                        matches!(conditional_atom(left), Some(MachineTerm::If { then_term, .. })
                        if matches!(then_term.as_ref(), MachineTerm::Binary { .. }))
                    );
                    assert!(
                        matches!(conditional_atom(right), Some(MachineTerm::If { else_term, .. })
                        if matches!(else_term.as_ref(), MachineTerm::Binary { .. }))
                    );
                    assert!(conditional_atom(left_miss).is_none());
                    assert!(conditional_atom(right_miss).is_none());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "{format:?}, {size} nested arithmetic nodes"
            );
        }
    }
}
