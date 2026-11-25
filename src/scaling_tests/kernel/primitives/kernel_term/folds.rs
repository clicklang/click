use super::*;

#[test]
fn fold_payload_construction_retains_growing_shared_bodies_with_constant_work() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|n| KernelTerm::variable(KernelType::Integer, Variable(950_000 + n)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut body = KernelTerm::variable(KernelType::Integer, Variable(960_000));
            for _ in 0..size {
                body = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![body.clone(), body],
                )
                .unwrap();
            }
            let zero = KernelTerm::integer_literal(0.into());
            let before = KernelTermExport::machine_export_count();
            let ((fold, copy), work) = crate::instrumentation::measure_deterministic_work(|| {
                let fold = KernelFold::new(
                    KernelFoldIndex::Integer,
                    Variable(960_000),
                    Variable(960_001),
                    [zero.clone(), zero.clone(), zero.clone(), body.clone()],
                )
                .unwrap();
                let copy = fold.clone();
                assert_eq!(fold, copy);
                (fold, copy)
            });
            assert_eq!(fold.arguments[3], body);
            assert_eq!(copy.arguments[3], body);
            assert_eq!(work, 1, "size={size}, unrelated={unrelated}");
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }
}

#[test]
fn nested_integer_fold_producers_keep_common_children_in_linear_work() {
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let index = IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::Variable(Variable(980001)).into(),
        };
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut value = IntegerTerm::Variable(Variable(980002));
            for _ in 0..size {
                value = IntegerTerm::range_fold(
                    index.clone(),
                    IntegerTerm::constant_i64(0),
                    Variable(980003),
                    Variable(980004),
                    value,
                );
            }
            value
        });
        let root = KernelTermImport::default().integer(&value.into());
        let mut node = &root;
        let mut folds = 0;
        while let KernelTermNode::Fold(fold) = node.node() {
            folds += 1;
            node = &fold.arguments[3];
        }
        assert_eq!(folds, size);
        assert!(work < 250 * size, "size={size}, work={work}");
    }
}

#[test]
fn nested_machine_fold_producers_retain_children_without_native_exports() {
    use crate::kernel::ExecutionValue;
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let zero = ExecutionValue::Native(ProgramValue::Int32(OldMachineTerm::constant(0)));
        let end = ExecutionValue::Native(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            981001,
        ))));
        let before = KernelTermExport::machine_export_count();
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut value = ExecutionValue::Native(ProgramValue::Int32(OldMachineTerm::Variable(
                Variable(981002),
            )));
            for _ in 0..size {
                value = crate::kernel::spec::symbolic_spec_range_fold_value(
                    zero.clone(),
                    end.clone(),
                    zero.clone(),
                    &"acc".into(),
                    &"item".into(),
                    value,
                )
                .unwrap();
            }
            value
        });
        let mut node = value.shared().expect("retained machine producer");
        let mut folds = 0;
        while let KernelTermNode::Fold(fold) = node.node() {
            folds += 1;
            node = &fold.arguments[3];
        }
        assert_eq!(folds, size);
        assert_eq!(KernelTermExport::machine_export_count(), before);
        assert!(work < 250 * size, "size={size}, work={work}");
    }
}

#[test]
fn empty_machine_fold_check_skips_growing_callback() {
    use crate::kernel::{MachineOperandView, PureFactContext};

    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let ty = KernelType::Program(ProgramType::Int32);
        let literal = |bits| {
            KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Old(&OldMachineTerm::constant(bits)),
            )
        };
        let start = literal(1);
        let end = literal((-3i32) as u32);
        let initial = literal(5);
        let mut facts = PureFactContext::new();
        for index in 0..unrelated {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(990_000 + index)),
                    OldMachineTerm::constant(13),
                ),
                true,
            );
        }
        for size in [16, 64, 256] {
            let accumulator = Variable(981_100);
            let item = Variable(981_101);
            let mut body = KernelTerm::variable(ty.clone(), accumulator);
            for _ in 0..size {
                body = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [body, initial.clone()],
                );
            }
            let fold = KernelFold::new(
                KernelFoldIndex::Int32,
                accumulator,
                item,
                [start.clone(), end.clone(), initial.clone(), body],
            )
            .unwrap()
            .into_term();
            let before = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.simplify_machine_operand_under_assumptions(
                    MachineOperandView::Shared(&fold),
                    format,
                )
            });
            assert_eq!(
                result.operand_view().literal(),
                Some(OldMachineTerm::constant(5))
            );
            assert_eq!(KernelTermExport::machine_export_count(), before);
            assert!(
                work <= 16,
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn literal_range_projection_check_ignores_trip_count() {
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let literal = |value: i32| {
        KernelTermImport::default().machine(format, &OldMachineTerm::constant(value as u32))
    };
    let [accumulator, item] = [Variable(981_200), Variable(981_201)];
    let variable = |id| KernelTerm::variable(KernelType::Program(ProgramType::Int32), id);
    let seed = variable(Variable(981_202));
    for (start, unrelated) in [(i32::MAX - 8, 0), (0, 64), (i32::MIN, 256)] {
        let mut facts = PureFactContext::new();
        for index in 0..unrelated {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    OldMachineTerm::Variable(Variable(981_300 + index)),
                    OldMachineTerm::constant(7),
                ),
                true,
            );
        }
        for (body, expected) in [
            (variable(item), literal(i32::MAX - 1)),
            (variable(accumulator), seed.clone()),
            (literal(-7), literal(-7)),
        ] {
            let fold = KernelFold::new(
                KernelFoldIndex::Int32,
                accumulator,
                item,
                [literal(start), literal(i32::MAX), seed.clone(), body],
            )
            .unwrap()
            .into_term();
            let before = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.simplify_machine_operand_under_assumptions(
                    MachineOperandView::Shared(&fold),
                    format,
                )
            });
            assert_eq!(result.shared_operand(), Some(&expected));
            assert!(work <= 24, "start={start}: {work}");
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }
}

#[test]
fn short_machine_fold_check_visits_shared_callback_once_per_step() {
    use crate::kernel::MachineOperandView;

    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let ty = KernelType::Program(ProgramType::Int32);
        let _unrelated = (0..unrelated)
            .map(|index| KernelTerm::variable(ty.clone(), Variable(990_000 + index)))
            .collect::<Vec<_>>();
        let literal = |bits| {
            KernelTerm::retained_machine_operand(
                format,
                MachineOperandView::Old(&OldMachineTerm::constant(bits)),
            )
        };
        let start = literal(0);
        let initial = literal(0);
        for size in [16, 64, 256] {
            let accumulator = Variable(981_100);
            let item = Variable(981_101);
            let mut body = KernelTerm::variable(ty.clone(), accumulator);
            for _ in 0..size {
                body = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [body.clone(), body],
                );
            }
            let fold = |end| {
                KernelFold::new(
                    KernelFoldIndex::Int32,
                    accumulator,
                    item,
                    [start.clone(), literal(end), initial.clone(), body.clone()],
                )
                .unwrap()
            };
            let short = fold(2);
            let long = fold(i32::MAX as u32);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| short.bounded_int32_result());
            assert_eq!(result, Some(initial.clone()));
            assert!(
                work <= 250 * size,
                "size={size}, unrelated={unrelated}, work={work}"
            );
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| long.bounded_int32_result());
            assert!(result.is_none());
            assert!(
                work <= 16,
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}
