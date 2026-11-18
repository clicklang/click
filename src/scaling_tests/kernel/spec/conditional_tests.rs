use super::*;
#[test]
fn growing_conditional_joins_and_observations_keep_shared_prefixes() {
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut value = variable(format, 998140);
        let zero = word(format, 0);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                value = join(
                    &ConditionTerm::Variable(Variable(998150 + index as u64)),
                    &value,
                    &zero,
                );
                assert!(value.observe().is_some());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < size * 100, "size={size}, work={work}");
    }
}

#[test]
fn selected_conditional_checks_retain_arms_at_every_machine_format() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let samples = [16usize, 64, 256].map(|size| {
            let _session = VerificationSession::enter();
            let guard = ConditionTerm::Variable(Variable(998190));
            let facts = PureFactContext::new().assume_condition(guard.clone(), true);
            let mut value = word(format, 1);
            let zero = word(format, 0);
            for _ in 0..size {
                value = join(&guard, &value, &zero);
            }
            let condition = ConditionTerm::integer_equal(
                value.observe().unwrap(),
                IntegerTerm::constant(1.into()),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(facts.decide(&condition), Some(true));
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            (size, work)
        });
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small <= sw * large * 2, "{format:?}: {samples:?}");
        }
    }
}

#[test]
fn identical_conditional_arms_normalize_without_revisiting_shared_suffixes() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let guard =
            KernelTermImport::default().condition(&ConditionTerm::Variable(Variable(998202)));
        let base = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998203));
        let mut root = base.clone();
        for _ in 0..size {
            root = KernelTerm::machine_if_shared(format, [guard.clone(), root.clone(), root]);
        }
        let condition = ConditionTerm::integer_equal(
            SpecValue::Shared(root).observe().unwrap(),
            SpecValue::Shared(base).observe().unwrap(),
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(PureFactContext::new().decide(&condition), Some(true));
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

#[test]
fn closed_comparison_conditionals_ignore_unrelated_facts() {
    for (operator, truth) in [
        (ComparisonOperator::LessThan, false),
        (ComparisonOperator::Equal, false),
        (ComparisonOperator::Equal, true),
        (ComparisonOperator::NotEqual, false),
        (ComparisonOperator::NotEqual, true),
    ] {
        let mut baseline = None;
        for size in [0, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts =
                    facts.assume_condition(ConditionTerm::Variable(Variable(999720 + index)), true);
            }
            let expression = closed_comparison_if(
                SpecExpression::Value(ProgramValue::UInt64(MachineTerm::Variable(Variable(
                    999710,
                )))),
                SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(3))),
                operator,
                truth,
            );
            let exports = KernelTermExport::machine_export_count();
            let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
                lower_closed_order_if(&expression, &facts)
            });
            let expected = lower_closed_order_if(&expression, &PureFactContext::new());
            assert_eq!(path.value, expected.value);
            let first = *baseline.get_or_insert(work);
            assert!(
                work <= first + 64,
                "{size} unrelated facts: {work}, baseline={first}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn nested_closed_comparison_conditionals_lower_with_linear_work() {
    for (operator, truth) in [
        (ComparisonOperator::LessThan, false),
        (ComparisonOperator::LessThan, true),
        (ComparisonOperator::Equal, false),
        (ComparisonOperator::Equal, true),
        (ComparisonOperator::NotEqual, false),
        (ComparisonOperator::NotEqual, true),
    ] {
        let mut samples = Vec::new();
        for size in [8, 32, 128, 512] {
            let _session = VerificationSession::enter();
            // Grow explicit source while keeping nesting logarithmic.
            let mut layer = (1..=size)
                .map(|n| {
                    SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(
                        n as u64,
                    )))
                })
                .collect::<Vec<_>>();
            while layer.len() > 1 {
                layer = layer
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| {
                        closed_comparison_if(pair[0].clone(), pair[1].clone(), operator, truth)
                    })
                    .collect();
            }
            let expression = layer.pop().unwrap();
            let exports = KernelTermExport::machine_export_count();
            let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
                lower_closed_order_if(&expression, &PureFactContext::new())
            });
            assert!(
                matches!(path.value, SpecValue::Shared(ref root) if matches!(root.node(), KernelTermNode::MachineIf { .. }))
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work < size * 512, "{size} conditionals: {work}");
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small <= sw * large * 2, "{truth}: {samples:?}");
        }
    }
}

#[test]
fn symbolic_comparisons_ignore_ambient_guard_facts() {
    for (operator, relation) in [
        (ComparisonOperator::LessThan, CompareRelation::LessThan),
        (ComparisonOperator::Equal, CompareRelation::Equal),
    ] {
        let mut baseline = None;
        let mut expected = None;
        for size in [0, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let value =
                |n| SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
            let guard_value = MachineTerm::Variable(Variable(999750));
            let guard = ConditionTerm::Compare {
                format: if relation == CompareRelation::Equal {
                    MachineIntegerType::Int64
                } else {
                    MachineIntegerType::UInt64
                },
                relation,
                left: Box::new(guard_value.clone()),
                right: Box::new(MachineTerm::uint64_constant(8)),
            };
            let proposition = SpecProposition::Comparison {
                left: SpecExpression::If {
                    condition: Box::new(SpecProposition::Comparison {
                        left: SpecExpression::Value(ProgramValue::UInt64(guard_value)),
                        operator,
                        right: value(8),
                    }),
                    then_branch: Box::new(value(9)),
                    else_branch: Box::new(value(3)),
                },
                operator: ComparisonOperator::LessEqual,
                right: value(100),
            };
            let state = ExecutionState::new();
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts =
                    facts.assume_condition(ConditionTerm::Variable(Variable(999760 + index)), true);
            }
            for truth in [None, Some(true), Some(false)] {
                let mut branch_facts = facts.clone();
                if let Some(truth) = truth {
                    branch_facts = branch_facts.assume_condition(guard.clone(), truth);
                }
                let exports = KernelTermExport::machine_export_count();
                let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let mut execution = ExecutionBudget::new();
                    lower_spec_proposition_at_state_with_algebraic_bindings_in(
                        SpecScope::unbound(&state, None),
                        &proposition,
                        &branch_facts,
                        &mut SpecEvaluation::logical(&mut execution),
                    )
                    .unwrap()
                });
                assert_eq!(paths.len(), 1);
                let actual = &paths[0].proposition;
                assert!(
                    matches!(&actual, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(), MachineTerm::If { .. }))))
                );
                assert_eq!(actual, expected.get_or_insert_with(|| actual.clone()));
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                let first = *baseline.get_or_insert(work);
                assert!(
                    work <= first + 64,
                    "{size} unrelated facts, guard={truth:?}: {work}, baseline={first}"
                );
            }
        }
    }
}

#[test]
fn boolean_guard_comparisons_ignore_ambient_flag_facts() {
    let mut baseline = None;
    let mut expected = None;
    for size in [0, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let guard = ConditionTerm::Variable(Variable(999800));
        let value =
            |n| SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
        let proposition = SpecProposition::Comparison {
            left: SpecExpression::If {
                condition: Box::new(SpecProposition::Comparison {
                    left: SpecExpression::Value(ProgramValue::of_bool(guard.clone())),
                    operator: ComparisonOperator::Equal,
                    right: SpecExpression::Value(ProgramValue::of_bool(ConditionTerm::Constant(
                        true,
                    ))),
                }),
                then_branch: Box::new(value(9)),
                else_branch: Box::new(value(3)),
            },
            operator: ComparisonOperator::LessEqual,
            right: value(100),
        };
        let state = ExecutionState::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(ConditionTerm::Variable(Variable(999810 + index)), true);
        }
        for truth in [None, Some(true), Some(false)] {
            let mut branch_facts = facts.clone();
            if let Some(truth) = truth {
                branch_facts = branch_facts.assume_condition(guard.clone(), truth);
            }
            let exports = KernelTermExport::machine_export_count();
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    SpecScope::unbound(&state, None),
                    &proposition,
                    &branch_facts,
                    &mut SpecEvaluation::logical(&mut execution),
                )
                .unwrap()
            });
            assert_eq!(paths.len(), 1);
            let actual = &paths[0].proposition;
            assert!(
                matches!(&actual, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(), MachineTerm::If { condition, .. } if condition.as_ref() == &guard))))
            );
            assert_eq!(actual, expected.get_or_insert_with(|| actual.clone()));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let first = *baseline.get_or_insert(work);
            assert!(
                work <= first + 64,
                "{size} unrelated facts, flag={truth:?}: {work}, baseline={first}"
            );
        }
    }
}

#[test]
fn reflexive_conditionals_ignore_unrelated_facts_and_value_aliases() {
    for operator in [ComparisonOperator::Equal, ComparisonOperator::LessThan] {
        let mut baseline = None;
        let mut expected = None;
        for size in [0, 16, 64, 256] {
            let _session = VerificationSession::enter();
            let variable = MachineTerm::Variable(Variable(999900));
            let value = || SpecExpression::Value(ProgramValue::UInt64(variable.clone()));
            let three =
                || SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(3)));
            let proposition = SpecProposition::Comparison {
                left: SpecExpression::If {
                    condition: Box::new(SpecProposition::Comparison {
                        left: value(),
                        operator,
                        right: value(),
                    }),
                    then_branch: Box::new(value()),
                    else_branch: Box::new(three()),
                },
                operator: ComparisonOperator::LessEqual,
                right: SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(
                    100,
                ))),
            };
            let mut facts = PureFactContext::new();
            for index in 0..size {
                facts =
                    facts.assume_condition(ConditionTerm::Variable(Variable(999910 + index)), true);
            }
            for alias in [false, true] {
                let mut branch_facts = facts.clone();
                if alias {
                    branch_facts = branch_facts.assume_condition(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: Box::new(variable.clone()),
                            right: Box::new(MachineTerm::uint64_constant(3)),
                        },
                        true,
                    );
                }
                let state = ExecutionState::new();
                let exports = KernelTermExport::machine_export_count();
                let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                    let mut execution = ExecutionBudget::new();
                    lower_spec_proposition_at_state_with_algebraic_bindings_in(
                        SpecScope::unbound(&state, None),
                        &proposition,
                        &branch_facts,
                        &mut SpecEvaluation::logical(&mut execution),
                    )
                    .unwrap()
                });
                assert_eq!(paths.len(), 1);
                let actual = &paths[0].proposition;
                assert!(
                    matches!(&actual, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(), MachineTerm::If { .. }))))
                );
                assert_eq!(actual, expected.get_or_insert_with(|| actual.clone()));
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                let first = *baseline.get_or_insert(work);
                assert!(
                    work <= first + 64,
                    "{size} facts, alias={alias}: {work}, baseline={first}"
                );
            }
        }
    }
}

#[test]
fn nested_reflexive_conditionals_lower_with_linear_work() {
    for operator in [ComparisonOperator::Equal, ComparisonOperator::LessThan] {
        let mut samples = Vec::new();
        for size in [8, 32, 128, 512] {
            let _session = VerificationSession::enter();
            let value =
                |n| SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
            let guard_value = SpecExpression::Value(ProgramValue::UInt64(MachineTerm::Variable(
                Variable(999960),
            )));
            let mut layer = (1..=size).map(|n| value(n as u64)).collect::<Vec<_>>();
            // Grow the explicit source, keeping nesting logarithmic.
            while layer.len() > 1 {
                layer = layer
                    .as_chunks::<2>().0.iter()
                    .map(|pair| SpecExpression::If {
                        condition: Box::new(SpecProposition::Comparison {
                            left: guard_value.clone(),
                            operator,
                            right: guard_value.clone(),
                        }),
                        then_branch: Box::new(pair[0].clone()),
                        else_branch: Box::new(pair[1].clone()),
                    })
                    .collect();
            }
            let expression = layer.pop().unwrap();
            let exports = KernelTermExport::machine_export_count();
            let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
                lower_closed_order_if(&expression, &PureFactContext::new())
            });
            assert!(
                matches!(path.value, SpecValue::Shared(ref root) if matches!(root.node(), KernelTermNode::MachineIf { .. }))
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work < size * 512, "{size} conditionals: {work}");
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small <= sw * large * 2, "{operator:?}: {samples:?}");
        }
    }
}

fn bitwise_arm_comparison(
    format: MachineIntegerType,
    operator: MachineBinaryOp,
    index: u64,
) -> SpecProposition {
    let value = |term| SpecExpression::Value(format.value_from_term(term));
    let word = |n: u64| {
        value(crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap())
    };
    let left = Box::new(value(MachineTerm::Variable(Variable(1_010_000 + index))));
    let right = Box::new(word(7));
    let arm = match operator {
        MachineBinaryOp::BitwiseAnd => SpecExpression::BitwiseAnd(left, right),
        MachineBinaryOp::BitwiseOr => SpecExpression::BitwiseOr(left, right),
        MachineBinaryOp::BitwiseXor => SpecExpression::BitwiseXor(left, right),
        _ => unreachable!(),
    };
    SpecProposition::Comparison {
        left: SpecExpression::If {
            condition: Box::new(SpecProposition::Comparison {
                left: SpecExpression::Value(ProgramValue::of_bool(ConditionTerm::Variable(
                    Variable(1_020_000 + index),
                ))),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(ProgramValue::of_bool(ConditionTerm::Constant(true))),
            }),
            then_branch: Box::new(arm),
            else_branch: Box::new(word(3)),
        },
        operator: ComparisonOperator::LessEqual,
        right: word(100),
    }
}

#[test]
fn bitwise_arm_comparisons_ignore_ambient_flag_and_operand_facts() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for operator in [
            MachineBinaryOp::BitwiseAnd,
            MachineBinaryOp::BitwiseOr,
            MachineBinaryOp::BitwiseXor,
        ] {
            let mut baseline = None;
            let mut expected = None;
            for size in [0, 16, 64, 256] {
                let _session = VerificationSession::enter();
                let state = ExecutionState::new();
                let proposition = bitwise_arm_comparison(format, operator, 0);
                let mut facts = PureFactContext::new();
                for index in 0..size {
                    facts = facts.assume_condition(
                        ConditionTerm::Variable(Variable(1_030_000 + index)),
                        true,
                    );
                }
                for truth in [None, Some(true), Some(false)] {
                    for alias in [false, true] {
                        let mut selected = facts.clone();
                        if let Some(truth) = truth {
                            selected = selected.assume_condition(
                                ConditionTerm::Variable(Variable(1_020_000)),
                                truth,
                            );
                        }
                        if alias {
                            selected = selected.assume_condition(
                                ConditionTerm::Compare {
                                    format: if format.format().bits() == 64 {
                                        MachineIntegerType::Int64
                                    } else {
                                        format
                                    },
                                    relation: CompareRelation::Equal,
                                    left: Box::new(MachineTerm::Variable(Variable(1_010_000))),
                                    right: Box::new(
                                        crate::kernel::machine_integer::range::constant_word(
                                            format,
                                            &0.into(),
                                        )
                                        .unwrap(),
                                    ),
                                },
                                true,
                            );
                        }
                        let exports = KernelTermExport::machine_export_count();
                        let (paths, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                let mut execution = ExecutionBudget::new();
                                lower_spec_proposition_at_state_with_algebraic_bindings_in(
                                    SpecScope::unbound(&state, None),
                                    &proposition,
                                    &selected,
                                    &mut SpecEvaluation::logical(&mut execution),
                                )
                                .unwrap()
                            });
                        assert_eq!(paths.len(), 1);
                        let actual = &paths[0].proposition;
                        assert!(
                            matches!(&actual, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(), MachineTerm::If { then_term, .. } if matches!(then_term.as_ref(), MachineTerm::Binary { .. })))))
                        );
                        assert_eq!(actual, expected.get_or_insert_with(|| actual.clone()));
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        let first = *baseline.get_or_insert(work);
                        assert!(
                            work <= first + 64,
                            "{format:?}: {size} facts, flag={truth:?}, alias={alias}: {work} vs {first}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn bitwise_arm_comparison_work_scales_with_explicit_source() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let state = ExecutionState::new();
        let source = (0..size)
            .map(|index| {
                bitwise_arm_comparison(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::BitwiseAnd,
                    index as u64,
                )
            })
            .collect::<Vec<_>>();
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for proposition in &source {
                let mut execution = ExecutionBudget::new();
                let paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    SpecScope::unbound(&state, None),
                    proposition,
                    &facts,
                    &mut SpecEvaluation::logical(&mut execution),
                )
                .unwrap();
                assert!(matches!(
                    &paths[0].proposition, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { .. }, _)))));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < size * 512, "{size} written comparisons: {work}");
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

fn bitwise_guard_comparison(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    index: u64,
) -> SpecProposition {
    let mut proposition = bitwise_arm_comparison(format, op, index);
    let SpecProposition::Comparison {
        left:
            SpecExpression::If {
                condition,
                then_branch,
                ..
            },
        ..
    } = &mut proposition
    else {
        unreachable!()
    };
    let bitwise = (**then_branch).clone();
    let variable = SpecExpression::Value(
        format.value_from_term(MachineTerm::Variable(Variable(1_040_000 + index))),
    );
    **condition = SpecProposition::Comparison {
        left: bitwise,
        operator: ComparisonOperator::LessThan,
        right: variable.clone(),
    };
    **then_branch = variable;
    proposition
}

#[test]
fn bitwise_guard_comparisons_ignore_ambient_truth_and_operand_aliases() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for op in [
            MachineBinaryOp::BitwiseAnd,
            MachineBinaryOp::BitwiseOr,
            MachineBinaryOp::BitwiseXor,
        ] {
            let mut expected = None;
            let mut baseline = None;
            for size in [0, 16, 64, 256] {
                let _session = VerificationSession::enter();
                let state = ExecutionState::new();
                let proposition = bitwise_guard_comparison(format, op, 0);
                let mut execution = ExecutionBudget::new();
                let original = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    SpecScope::unbound(&state, None),
                    &proposition,
                    &PureFactContext::new(),
                    &mut SpecEvaluation::logical(&mut execution),
                )
                .unwrap();
                let Some((ConditionTerm::Compare { left, .. }, true)) =
                    original[0].proposition.condition_native()
                else {
                    panic!("native comparison");
                };
                let MachineTerm::If { condition, .. } = left.as_ref() else {
                    panic!("retained conditional");
                };
                let guard = condition.as_ref().clone();
                let mut facts = PureFactContext::new();
                for index in 0..size {
                    facts = facts.assume_condition(
                        ConditionTerm::Variable(Variable(1_050_000 + index)),
                        true,
                    );
                }
                for truth in [None, Some(true), Some(false)] {
                    for alias in [false, true] {
                        let mut selected = facts.clone();
                        if let Some(truth) = truth {
                            selected = selected.assume_condition(guard.clone(), truth);
                        }
                        if alias {
                            selected = selected.assume_condition(
                                ConditionTerm::Compare {
                                    format: if format.format().bits() == 64 {
                                        MachineIntegerType::Int64
                                    } else {
                                        format
                                    },
                                    relation: CompareRelation::Equal,
                                    left: Box::new(MachineTerm::Variable(Variable(1_010_000))),
                                    right: Box::new(
                                        crate::kernel::machine_integer::range::constant_word(
                                            format,
                                            &0.into(),
                                        )
                                        .unwrap(),
                                    ),
                                },
                                true,
                            );
                        }
                        let exports = KernelTermExport::machine_export_count();
                        let (paths, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                let mut budget = ExecutionBudget::new();
                                lower_spec_proposition_at_state_with_algebraic_bindings_in(
                                    SpecScope::unbound(&state, None),
                                    &proposition,
                                    &selected,
                                    &mut SpecEvaluation::logical(&mut budget),
                                )
                                .unwrap()
                            });
                        assert_eq!(paths.len(), 1);
                        let actual = &paths[0].proposition;
                        assert!(
                            matches!(&actual, condition_source_0 @ Proposition::ConditionIs(_,true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(),MachineTerm::If { condition, .. } if matches!(condition.as_ref(), ConditionTerm::Compare { .. })))))
                        );
                        assert_eq!(actual, expected.get_or_insert_with(|| actual.clone()));
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        let first = *baseline.get_or_insert(work);
                        assert!(
                            work <= first + 64,
                            "{format:?}, {op:?}, {size} facts, truth={truth:?}, alias={alias}: {work} vs {first}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn bitwise_guard_comparison_work_scales_with_written_source() {
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let _session = VerificationSession::enter();
        let state = ExecutionState::new();
        let source = (0..size)
            .map(|i| {
                bitwise_guard_comparison(
                    MachineIntegerType::UInt64,
                    MachineBinaryOp::BitwiseAnd,
                    i as u64,
                )
            })
            .collect::<Vec<_>>();
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for proposition in &source {
                let mut budget = ExecutionBudget::new();
                let paths = lower_spec_proposition_at_state_with_algebraic_bindings_in(
                    SpecScope::unbound(&state, None),
                    proposition,
                    &facts,
                    &mut SpecEvaluation::logical(&mut budget),
                )
                .unwrap();
                assert!(matches!(
                    &paths[0].proposition, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { .. }, _)))));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < size * 512, "{size} guards: {work}");
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}
