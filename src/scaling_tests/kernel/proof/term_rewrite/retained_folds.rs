use super::*;

#[test]
fn common_fold_rewrite_scales_with_shared_children_without_machine_exports() {
    for integer in [false, true] {
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let format = MachineIntegerType::Int32;
            let mut body = if integer {
                KernelTerm::variable(KernelType::Integer, Variable(70))
            } else {
                KernelTerm::retained_machine_operand(
                    format,
                    MachineOperandView::Legacy(&MachineTerm::Variable(Variable(70))),
                )
            };
            for _ in 0..size {
                body = if integer {
                    KernelTerm::integer_operation(
                        KernelIntegerOperator::Add,
                        vec![body.clone(), body],
                    )
                    .unwrap()
                } else {
                    KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [body.clone(), body],
                    )
                };
            }
            let zero = if integer {
                KernelTerm::integer_literal(0.into())
            } else {
                KernelTerm::retained_machine_operand(
                    format,
                    MachineOperandView::Legacy(&MachineTerm::constant(0)),
                )
            };
            let fold = KernelFold::new(
                if integer {
                    KernelFoldIndex::Integer
                } else {
                    KernelFoldIndex::Int32
                },
                Variable(71),
                Variable(72),
                [zero.clone(), zero, body.clone(), body],
            )
            .unwrap();
            let from = MachineTerm::Variable(Variable(90));
            let to = MachineTerm::Variable(Variable(91));
            let mut rewrite = TermRewrite::for_bits(&from, &to);
            let exports = KernelTermExport::machine_export_count();
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            assert_eq!(result.unwrap(), fold);
            assert!(
                work <= 100 * size + 200,
                "integer={integer} size={size} work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let (result, repeat_work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            assert_eq!(result.unwrap(), fold);
            assert!(
                repeat_work <= 30,
                "integer={integer} size={size} repeat={repeat_work}"
            );
        }
    }
}

#[test]
fn integer_fold_capture_summary_scales_without_integer_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Variable(91_000);
        let accumulator = Variable(91_001);
        let item = Variable(91_002);
        let mut body = KernelTerm::variable(KernelType::Integer, source);
        for index in 0..size {
            let term =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
            body = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![
                    term,
                    KernelTerm::variable(KernelType::Integer, Variable(92_000 + index)),
                ],
            )
            .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            accumulator,
            item,
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();

        let samples = [0, 16, 64, 256].map(|unrelated| {
            let replacement = IntegerTerm::Variable(accumulator);
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            for index in 0..unrelated {
                let other = KernelTerm::variable(KernelType::Integer, Variable(95_000 + index));
                assert_eq!(rewrite.body_variable_max(&other), Some(95_000 + index));
            }
            let exports = KernelTermExport::integer_export_count();
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            let result = result.unwrap();
            assert!(result.accumulator.0 > 92_000 + size - 1);
            assert_eq!(result.item, item);
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
        assert!(
            samples[0] <= 160 * size as usize + 400,
            "size={size}, work={samples:?}"
        );
    }
}

#[test]
fn nested_integer_fold_rewrites_keep_shared_bodies_and_scopes() {
    for capture in [false, true] {
        for depth in [4, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let source = Variable(96_000);
            let accumulator = Variable(96_001);
            let item = Variable(96_002);
            let replacement = if capture {
                accumulator
            } else {
                Variable(96_003)
            };
            let var = |variable| KernelTerm::variable(KernelType::Integer, variable);
            let add = |left, right| {
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![left, right])
                    .unwrap()
            };
            let make_fold = |body| {
                KernelFold::new(
                    KernelFoldIndex::Integer,
                    accumulator,
                    item,
                    [var(accumulator), var(accumulator), var(source), body],
                )
                .unwrap()
            };
            let mut fold = make_fold(add(var(accumulator), var(source)));
            for _ in 1..depth {
                let child = fold.into_term();
                fold = make_fold(add(child.clone(), child));
            }

            let samples = [0, 16, 64, 256].map(|unrelated| {
                let replacement_term = IntegerTerm::Variable(replacement);
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    source,
                    &replacement_term,
                    false,
                    &renamings,
                );
                for index in 0..unrelated {
                    let other = var(Variable(97_000 + index));
                    assert_eq!(rewrite.shared_fold_integer_child(&other), Some(other));
                }
                let exports = KernelTermExport::integer_export_count();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    rewrite.retained_fold(&fold)
                });
                let result = result.unwrap();
                assert_eq!(KernelTermExport::integer_export_count(), exports);

                let mut outer = accumulator;
                let mut current = &result;
                for level in 0..depth {
                    assert_eq!(current.arguments[0], var(outer));
                    assert_eq!(current.arguments[1], var(outer));
                    assert_eq!(current.arguments[2], var(replacement));
                    assert_eq!(current.item, item);
                    assert_eq!(current.accumulator != accumulator, capture);
                    if capture {
                        assert_ne!(current.accumulator, outer);
                    }
                    outer = current.accumulator;

                    let KernelTermNode::IntegerOperation { arguments, .. } =
                        current.arguments[3].node()
                    else {
                        panic!("expected retained addition");
                    };
                    if level + 1 == depth {
                        assert_eq!(arguments, &[var(outer), var(replacement)]);
                        break;
                    }
                    assert_eq!(arguments[0], arguments[1]);
                    let KernelTermNode::Fold(nested) = arguments[0].node() else {
                        panic!("expected retained nested fold");
                    };
                    current = nested;
                }
                work
            });
            assert!(
                samples.iter().all(|work| *work == samples[0]),
                "{samples:?}"
            );
            assert!(
                samples[0] <= 200 * depth + 400,
                "capture={capture} depth={depth} work={samples:?}"
            );
        }
    }
}

#[test]
fn literal_integer_conditionals_in_folds_keep_retained_arms() {
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Variable(98_000);
        let accumulator = Variable(98_001);
        let item = Variable(98_002);
        let value = KernelTerm::variable(KernelType::Integer, source);
        let zero = KernelTerm::integer_literal(0.into());
        let guard = KernelTermImport::default().condition(&ConditionTerm::Constant(false));
        let mut body = value.clone();
        for _ in 0..depth {
            body = KernelTerm::integer_if_raw([guard.clone(), body.clone(), body]);
        }

        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            accumulator,
            item,
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();
        let samples = [0, 16, 64, 256].map(|unrelated| {
            let replacement = IntegerTerm::Variable(accumulator);
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            for index in 0..unrelated {
                let other = KernelTerm::variable(KernelType::Integer, Variable(99_000 + index));
                assert_eq!(rewrite.shared_fold_integer_child(&other), Some(other));
            }

            let exports = KernelTermExport::integer_export_count();
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            let result = result.unwrap();
            assert_ne!(result.accumulator, accumulator);
            assert_eq!(KernelTermExport::integer_export_count(), exports);

            // Integer substitution preserves written closed guards, even
            // when the two arms coincide. The replacement stays free.
            let mut body = &result.arguments[3];
            for _ in 0..depth {
                let KernelTermNode::IntegerIf {
                    arguments: [condition, yes, no],
                } = body.node()
                else {
                    panic!("expected retained conditional");
                };
                assert_eq!(*condition, guard);
                assert_eq!(yes, no);
                body = yes;
            }
            assert_eq!(
                *body,
                KernelTerm::variable(KernelType::Integer, accumulator)
            );

            // A rewrite that simplifies closed guards keeps the selected arm.
            let mut simplify = TermRewrite::empty();
            let exports = KernelTermExport::integer_export_count();
            assert_eq!(simplify.retained_fold(&fold).unwrap().arguments[3], value);
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
        assert!(
            samples[0] <= 100 * depth + 400,
            "depth={depth}, work={samples:?}"
        );
    }
}

#[test]
fn boolean_variable_guards_in_integer_folds_select_retained_arms() {
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(99_500);
        let guard = KernelTerm::variable(KernelType::Bool, variable);
        let selected = KernelTerm::variable(KernelType::Integer, Variable(99_501));
        let zero = KernelTerm::integer_literal(0.into());
        let mut body = selected.clone();
        for index in 1..=depth {
            let other = KernelTerm::integer_literal(index.into());
            body = KernelTerm::integer_if_raw([guard.clone(), body, other]);
        }
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            Variable(99_502),
            Variable(99_503),
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();

        for (truth, expected) in [
            (true, selected),
            (false, KernelTerm::integer_literal(depth.into())),
        ] {
            let program = BTreeMap::from([(
                variable,
                TypedProgramValueReplacement::Bitvector(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::Constant(truth),
                )),
            )]);
            let integers = BTreeMap::new();
            let algebraic = BTreeMap::new();
            let samples = [0, 16, 64, 256].map(|unrelated| {
                let mut rewrite = TermRewrite::for_typed_variables(&program, &integers, &algebraic);
                for index in 0..unrelated {
                    let other =
                        KernelTerm::variable(KernelType::Integer, Variable(100_000 + index));
                    assert_eq!(rewrite.shared_fold_integer_child(&other), Some(other));
                }
                let exports = KernelTermExport::integer_export_count();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    rewrite.retained_fold(&fold)
                });
                assert_eq!(result.unwrap().arguments[3], expected);
                assert_eq!(KernelTermExport::integer_export_count(), exports);
                work
            });
            assert!(
                samples.iter().all(|work| *work == samples[0]),
                "{samples:?}"
            );
            assert!(
                samples[0] <= 100 * depth + 400,
                "depth={depth}, work={samples:?}"
            );
        }

        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::empty().retained_fold(&fold)
        });
        assert_eq!(result.unwrap(), fold);
        assert!(
            work <= 100 * depth + 400,
            "depth={depth}, unresolved work={work}"
        );
    }
}

#[test]
fn literal_machine_guards_in_integer_folds_keep_retained_arms() {
    let guards = [
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(MachineTerm::constant(u32::MAX)),
            right: Box::new(MachineTerm::constant(0)),
        },
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: Box::new(MachineTerm::constant(i32::MAX as u32)),
            right: Box::new(MachineTerm::constant(1)),
        },
    ];
    for depth in [16, 64, 256] {
        for native_guard in &guards {
            let _session = crate::kernel::VerificationSession::enter();
            let guard = KernelTermImport::default().condition(native_guard);
            let source = Variable(101_000);
            let value = KernelTerm::variable(KernelType::Integer, source);
            let zero = KernelTerm::integer_literal(0.into());
            let mut body = value.clone();
            for _ in 0..depth {
                body = KernelTerm::integer_if_raw([guard.clone(), body.clone(), body]);
            }
            let fold = KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(101_001),
                Variable(101_002),
                [zero.clone(), zero.clone(), zero, body],
            )
            .unwrap();
            let samples = [0, 16, 64, 256].map(|unrelated| {
                let mut rewrite = TermRewrite::empty();
                for index in 0..unrelated {
                    let other =
                        KernelTerm::variable(KernelType::Integer, Variable(101_100 + index));
                    assert_eq!(rewrite.shared_fold_integer_child(&other), Some(other));
                }
                let exports = KernelTermExport::integer_export_count();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    rewrite.retained_fold(&fold)
                });
                assert_eq!(result.unwrap().arguments[3], value);
                assert_eq!(KernelTermExport::integer_export_count(), exports);
                work
            });
            assert!(
                samples.iter().all(|work| *work == samples[0]),
                "{samples:?}"
            );
            assert!(
                samples[0] <= 100 * depth + 400,
                "depth={depth}, work={samples:?}"
            );
        }
    }
}
