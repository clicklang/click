use super::*;

#[test]
fn c_expression_handoffs_retain_growing_arithmetic_without_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::Variable(
            Variable(998270),
        )));
        for _ in 0..size {
            expression = ProgramExpression::Multiply(
                Box::new(expression),
                Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::uint32_constant(3),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| evaluate(&expression));
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            ExpressionOutcome::Value(ExecutionValue::Shared(_))
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn c_conditional_handoffs_keep_machine_results_without_exporting_prefixes() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = ProgramExpression::Multiply(
            Box::new(ProgramExpression::Value(ProgramValue::UInt64(
                MachineTerm::Variable(Variable(998271)),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::UInt64(
                MachineTerm::uint64_constant(3),
            ))),
        );
        for _ in 0..size {
            expression = ProgramExpression::Ternary {
                condition: Box::new(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::constant(1),
                ))),
                then_branch: Box::new(expression),
                else_branch: Box::new(ProgramExpression::Variable("unselected".into())),
            };
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| evaluate(&expression));
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            ExpressionOutcome::Value(ExecutionValue::Shared(_))
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn rust_expression_handoffs_retain_growing_narrow_and_shift_results() {
    for narrow in [false, true] {
        let mut work = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut expression = ProgramExpression::Value(ProgramValue::UInt8(
                MachineTerm::Variable(Variable(998304)),
            ));
            for _ in 0..size {
                expression = if narrow {
                    narrow_expression(
                        ProgramExpression::Multiply(
                            Box::new(expression),
                            Box::new(ProgramExpression::Value(ProgramValue::UInt8(
                                MachineTerm::narrow_constant(MachineIntegerType::UInt8, 3),
                            ))),
                        ),
                        ProgramType::UInt8,
                    )
                } else {
                    ProgramExpression::RustShiftRight(
                        Box::new(expression),
                        Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                            MachineTerm::uint32_constant(1),
                        ))),
                    )
                };
            }
            let exports = KernelTermExport::machine_export_count();
            let (paths, measured) =
                crate::instrumentation::measure_deterministic_work(|| evaluate(&expression));
            assert_eq!(paths.len(), 1);
            assert!(matches!(
                &paths[0].outcome,
                ExpressionOutcome::Value(ExecutionValue::Shared(_))
            ));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            work.push(measured);
        }
        assert!(
            work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
            "{work:?}"
        );
    }
}

#[test]
fn retained_local_assignment_and_readback_scale_without_prefix_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = ExecutionState::new().with_local(
            "held",
            ProgramValue::UInt32(MachineTerm::Variable(Variable(998321))),
        );
        let assignment = ProgramStatement::Assign {
            name: "held".into(),
            expression: ProgramExpression::Multiply(
                Box::new(ProgramExpression::Variable("held".into())),
                Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::uint32_constant(3),
                ))),
            ),
            source: Default::default(),
            prior_result: None,
        };
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let outcome = super::super::super::statements::execute_execution_statement(
                    &state,
                    &assignment,
                    &PureFactContext::new(),
                )
                .unwrap();
                let StatementOutcome::Normal(after) = outcome else {
                    panic!("local assignment");
                };
                state = *after;
            }
        });
        assert!(state.locals.get("held").unwrap().shared().is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn retained_return_and_caller_receipt_do_not_export_growing_prefixes() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(998331)));
        let three = KernelTermImport::default().machine(format, &MachineTerm::uint32_constant(3));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [root, three.clone()],
            );
        }
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "held",
            ExecutionValue::from(root.clone()),
            ProgramType::UInt32,
            false,
            false,
            false,
            false,
        );
        let statement = ProgramStatement::Return(ProgramExpression::Variable("held".into()));
        let function = program_function(
            ProgramType::UInt32,
            "handoff",
            Vec::new(),
            statement.clone(),
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let StatementOutcome::Return { value, .. } =
                    super::super::super::statements::execute_execution_statement(
                        &state,
                        &statement,
                        &PureFactContext::new(),
                    )
                    .unwrap()
                else {
                    panic!("return");
                };
                let mut obligations = Vec::new();
                let value = crate::kernel::functions::coerce_retained_function_return_value(
                    value,
                    &function,
                    &mut obligations,
                    &PureFactContext::new(),
                )
                .unwrap();
                crate::kernel::loops::assign_call_result(
                    &mut state,
                    &("received").into(),
                    value,
                    &mut obligations,
                    &PureFactContext::new(),
                )
                .unwrap();
                assert!(obligations.is_empty());
            }
        });
        assert_eq!(state.locals.get("received").unwrap().shared(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn complete_c_and_rust_machine_handoffs_retain_roots_without_prefix_exports() {
    for rust in [false, true] {
        let mut work = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (environment, statement) = complete_machine_handoff_program(rust, size, false);
            let caller = machine_handoff_caller(rust);
            let exports = KernelTermExport::machine_export_count();
            let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
                super::super::super::statements::execute_execution_statement_paths(
                    &caller,
                    &statement,
                    &PureFactContext::new(),
                    ExecutionContext::verify_loops(&environment),
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
            });
            let [path] = paths.as_slice() else {
                panic!("one complete machine path");
            };
            let StatementOutcome::Return { value, state } = &path.outcome else {
                panic!("machine return: {:?}", path.outcome);
            };
            assert!(path.obligations.is_empty(), "{:?}", path.obligations);
            assert!(value.shared().is_some());
            assert_eq!(
                value.shared(),
                state.locals.get("received").unwrap().shared()
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            work.push(measured);
        }
        assert!(
            work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
            "rust={rust}: {work:?}"
        );
    }
}

#[test]
fn retained_pointer_step_receipts_do_not_walk_dags_or_sibling_results() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = ExecutionState::new();
        for n in 0..unrelated {
            state.set_step_result(1000 + n, ProgramValue::Int32(MachineTerm::constant(n)));
        }
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1027950));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    Op::Add,
                    [argument.clone(), argument],
                );
            }
            let root = KernelTerm::shared_pointer_call(
                KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "step".into(),
                    vec![argument],
                ),
                SharedPointerValue::import(&Pointer::new(
                    Address::symbolic(Variable(1027951)),
                    ProgramType::Int32Pointer,
                )),
            );
            state.set_retained_step_result(11, root.clone().into());
            let expression = ProgramExpression::StepResult {
                step: 11,
                origin: crate::kernel::StepOrigin::Call("step".into()),
                ends: true,
            };
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..16 {
                    let paths = evaluate_expression_value_paths(
                        &state,
                        &expression,
                        &PureFactContext::new(),
                        &mut ExecutionBudget::new(),
                    )
                    .unwrap();
                    let ExpressionOutcome::Value(value) = &paths[0].outcome else {
                        panic!("step receipt")
                    };
                    assert_eq!(value.shared(), Some(&root));
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 64, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn click_negation_handoffs_retain_integer_operands_without_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::Variable(
            Variable(998270),
        )));
        for _ in 0..size {
            expression = ProgramExpression::Negate(Box::new(expression));
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| evaluate(&expression));
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            ExpressionOutcome::Value(ExecutionValue::Shared(_))
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn float_steps_and_returns_keep_shared_roots_without_exporting_prefixes() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = crate::kernel::KernelFloatType::Float64;
        let mut root = KernelTerm::variable(
            KernelType::Program(format.program_type()),
            Variable(1008302),
        );
        for _ in 0..size {
            root = KernelTerm::float_call(
                format,
                "float_step".into(),
                vec![(root.clone(), None), (root, None)],
            );
        }
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "x",
            ExecutionValue::Shared(root.clone()),
            format.program_type(),
            false,
            false,
            false,
            false,
        );
        let exports = KernelTermExport::float_export_count();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for value_type in [None, Some(format.program_type())] {
                let statement = ProgramStatement::StepValue {
                    aggregate_layout: None,
                    steps: vec![11],
                    expression: ProgramExpression::Variable("x".into()),
                    value_type,
                    pointee_constant: false,
                };
                let outcome = super::super::super::statements::execute_execution_statement(
                    &state,
                    &statement,
                    &PureFactContext::new(),
                )
                .unwrap();
                let StatementOutcome::Normal(after) = outcome else {
                    panic!("step result");
                };
                let expression = ProgramExpression::StepResult {
                    step: 11,
                    origin: crate::kernel::StepOrigin::Operator(
                        crate::kernel::OperatorKind::Ternary,
                    ),
                    ends: true,
                };
                let paths = evaluate_expression_value_paths(
                    &after,
                    &expression,
                    &PureFactContext::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                let ExpressionOutcome::Value(value) = &paths[0].outcome else {
                    panic!("retained step");
                };
                assert_eq!(value.shared(), Some(&root));
                let outcome = super::super::super::statements::execute_execution_statement(
                    &after,
                    &ProgramStatement::Return(expression),
                    &PureFactContext::new(),
                )
                .unwrap();
                let StatementOutcome::Return { value, .. } = outcome else {
                    panic!("return result");
                };
                assert_eq!(value.shared(), Some(&root));
            }
        });
        assert_eq!(KernelTermExport::float_export_count(), exports);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost <= costs[0] * 2), "{costs:?}");
}
