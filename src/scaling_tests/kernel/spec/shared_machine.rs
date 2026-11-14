use super::*;

#[test]
fn unsigned_production_and_single_export_are_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(980000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut expression = SpecExpression::Value(ProgramValue::UInt64(
                MachineTerm::Variable(Variable(981000)),
            ));
            for _ in 0..size {
                expression = SpecExpression::Add(
                    Box::new(expression),
                    Box::new(SpecExpression::Value(ProgramValue::UInt64(
                        MachineTerm::uint64_constant(1),
                    ))),
                );
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                let term = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                    .unwrap()
                    .unwrap();
                KernelTermExport::default().argument(&term.value).unwrap()
            });
            assert!(
                work <= 16 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn shared_arithmetic_children_are_not_reimported_or_expanded_during_construction() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        for size in [16, 64, 256] {
            let mut term = KernelTerm::variable(KernelType::C(format.c_type()), Variable(982000));
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Multiply,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    assert_eq!(term.children()[0], term.children()[1]);
                }
            });
            assert!(work <= 4 * size, "size={size}, work={work}");
        }
    }
}

#[test]
fn signed_available_operand_production_is_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(984000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut operand = MachineTerm::Variable(Variable(985000));
            for _ in 0..size {
                operand = MachineTerm::Binary {
                    format: MachineIntegerType::Int64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(operand),
                    right: Box::new(MachineTerm::int64_constant(1)),
                };
            }
            let expression = SpecExpression::Add(
                Box::new(SpecExpression::Value(ProgramValue::Int64(operand))),
                Box::new(SpecExpression::Value(ProgramValue::Int64(
                    MachineTerm::int64_constant(1),
                ))),
            );
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                let prepared = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                    .unwrap()
                    .unwrap();
                assert_eq!(prepared.obligations.len(), 1);
                KernelTermExport::default()
                    .argument(&prepared.value)
                    .unwrap()
            });
            assert!(
                work <= 32 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn nested_signed_preparation_retains_obligations_without_prefix_exports() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let leaf =
                || SpecExpression::Value(wrap(format, MachineTerm::Variable(Variable(986000))));
            let mut expression = leaf();
            for _ in 0..size {
                expression = SpecExpression::Add(Box::new(expression), Box::new(leaf()));
            }
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                    .unwrap()
                    .unwrap()
            });
            assert_eq!(result.obligations.len(), size);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(previous_work) = previous {
                assert!(
                    work <= 5 * previous_work,
                    "fourfold input growth must remain near linear: format={format:?}, size={size}, previous={previous_work}, work={work}"
                );
            }
            previous = Some(work);
        }
    }
}

#[test]
fn a_deferred_operand_rejects_one_preparation_without_importing_prefixes() {
    for size in [16, 64, 256] {
        let mut expression = SpecExpression::Value(ProgramValue::UInt64(MachineTerm::Variable(
            Variable(983000),
        )));
        for _ in 0..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::UInt64(
                    MachineTerm::uint64_constant(1),
                ))),
            );
        }
        let expression = SpecExpression::Add(
            Box::new(expression),
            Box::new(SpecExpression::ProgramExpression(
                ProgramExpression::Variable("later".into()),
            )),
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            prepare(&expression, &mut SpecEvaluation::logical(&mut execution)).unwrap()
        });
        assert!(result.is_none());
        // One visit and one interruption checkpoint per source node.
        assert_eq!(work, 2 * (2 * size + 3));
    }
}

#[test]
fn partial_division_production_retains_prefixes_and_debts() {
    for defined in [false, true] {
        let mut costs = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut expression =
                SpecExpression::Value(ProgramValue::Int64(MachineTerm::Variable(Variable(991910))));
            for _ in 0..size {
                expression = SpecExpression::Divide(
                    Box::new(expression),
                    Box::new(SpecExpression::Value(ProgramValue::Int64(
                        MachineTerm::Variable(Variable(991911)),
                    ))),
                );
            }
            let exports = KernelTermExport::machine_export_count();
            let (prepared, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut execution = ExecutionBudget::new();
                let mut budget = SpecEvaluation::logical(&mut execution);
                budget.c_definedness = defined;
                prepare(&expression, &mut budget).unwrap().unwrap()
            });
            assert_eq!(prepared.obligations.len(), size);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            costs.push(work);
        }
        assert!(costs[1] <= costs[0] * 5, "{costs:?}");
        assert!(costs[2] <= costs[1] * 5, "{costs:?}");
    }
}

#[test]
fn signed_shift_production_retains_prefixes_and_debts() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression =
            SpecExpression::Value(ProgramValue::Int64(MachineTerm::Variable(Variable(991920))));
        for _ in 0..size {
            expression = SpecExpression::ShiftLeft(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::Int64(
                    MachineTerm::Variable(Variable(991921)),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (prepared, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                .unwrap()
                .unwrap()
        });
        assert_eq!(prepared.obligations.len(), size);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        costs.push(work);
    }
    assert!(costs[1] <= costs[0] * 5, "{costs:?}");
    assert!(costs[2] <= costs[1] * 5, "{costs:?}");
}

#[test]
fn deferred_results_and_integer_observations_retain_growing_prefixes() {
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new().with_local(
            "x",
            ProgramValue::UInt64(MachineTerm::Variable(Variable(992200))),
        );
        let mut expression =
            SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        for _ in 0..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::UInt64(
                    MachineTerm::uint64_constant(1),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::unbound(&state, None),
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].value, SpecValue::Shared(_)));
        let observed = paths[0].value.observe().unwrap();
        assert!(matches!(observed, IntegerTerm::Machine(_)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn opaque_results_observe_and_compare_without_expanding_prefixes() {
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let leaf = MachineTerm::opaque_conversion(
            "retained_opaque",
            MachineTerm::Variable(Variable(992230)),
        );
        let mut root = KernelTerm::retained_native_machine_operand(format, &leaf);
        let one =
            KernelTerm::retained_native_machine_operand(format, &MachineTerm::uint64_constant(1));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), one.clone()],
                );
                let value = SpecValue::Shared(root.clone());
                assert!(value.observe().is_some());
                assert!(
                    value
                        .comparison(CComparisonOperator::Equal, &value)
                        .unwrap()
                        .is_some()
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(work <= previous * 5, "{size}: {work}, previous={previous}");
        }
        previous = Some(work);
    }
}

#[test]
fn deferred_opaque_shift_domains_keep_shared_prefixes() {
    for op in [
        MachineBinaryOp::ShiftLeft,
        MachineBinaryOp::ShiftRight,
        MachineBinaryOp::Divide,
    ] {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let format = MachineIntegerType::UInt64;
            let leaf = MachineTerm::opaque_conversion(
                "deferred_domain",
                MachineTerm::Variable(Variable(992240)),
            );
            let mut value =
                SpecValue::Shared(KernelTerm::retained_native_machine_operand(format, &leaf));
            let right = SpecValue::Native(ProgramValue::UInt64(MachineTerm::Variable(Variable(
                992241,
            ))));
            let mut execution = ExecutionBudget::new();
            let mut budget = SpecEvaluation::logical(&mut execution);
            budget.c_definedness = true;
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    let result = apply_values(Some(op), &value, &right, &budget).unwrap();
                    assert!(!result.obligations.is_empty());
                    value = SpecValue::Shared(result.value);
                    assert!(value.observe().is_some());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(previous) = previous {
                assert!(
                    work <= previous * 5,
                    "{op:?}: size={size}, work={work}, previous={previous}"
                );
            }
            previous = Some(work);
        }
    }
}

#[test]
fn same_format_casts_keep_deferred_prefixes_and_obligations() {
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new().with_local(
            "x",
            ProgramValue::UInt64(MachineTerm::Variable(Variable(992200))),
        );
        let mut expression =
            SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        for _ in 0..size {
            expression = SpecExpression::Cast(
                Box::new(SpecExpression::Add(
                    Box::new(expression),
                    Box::new(SpecExpression::Value(ProgramValue::UInt64(
                        MachineTerm::uint64_constant(1),
                    ))),
                )),
                ProgramType::UInt64,
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::unbound(&state, None),
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].value, SpecValue::Shared(_)));
        let observed = paths[0].value.observe().unwrap();
        assert!(matches!(observed, IntegerTerm::Machine(_)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous = Some(work);
    }
}
