use super::*;

#[test]
fn c_expression_handoffs_retain_growing_arithmetic_without_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression =
            CExpression::Value(CValue::UInt32(MachineTerm::Variable(Variable(998270))));
        for _ in 0..size {
            expression = CExpression::Multiply(
                Box::new(expression),
                Box::new(CExpression::Value(CValue::UInt32(
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
            CExpressionOutcome::Value(ExecutionValue::Shared(_))
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
        let mut expression = CExpression::Multiply(
            Box::new(CExpression::Value(CValue::UInt64(MachineTerm::Variable(
                Variable(998271),
            )))),
            Box::new(CExpression::Value(CValue::UInt64(
                MachineTerm::uint64_constant(3),
            ))),
        );
        for _ in 0..size {
            expression = CExpression::Conditional {
                condition: Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(1)))),
                then_branch: Box::new(expression),
                else_branch: Box::new(CExpression::Variable("unselected".into())),
            };
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| evaluate(&expression));
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            &paths[0].outcome,
            CExpressionOutcome::Value(ExecutionValue::Shared(_))
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
            let mut expression =
                CExpression::Value(CValue::UInt8(MachineTerm::Variable(Variable(998304))));
            for _ in 0..size {
                expression = if narrow {
                    narrow_expression(
                        CExpression::Multiply(
                            Box::new(expression),
                            Box::new(CExpression::Value(CValue::UInt8(
                                MachineTerm::narrow_constant(MachineIntegerType::UInt8, 3),
                            ))),
                        ),
                        CType::UInt8,
                    )
                } else {
                    CExpression::RustShiftRight(
                        Box::new(expression),
                        Box::new(CExpression::Value(CValue::UInt32(
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
                CExpressionOutcome::Value(ExecutionValue::Shared(_))
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
        let mut state = CState::new().with_local(
            "held",
            CValue::UInt32(MachineTerm::Variable(Variable(998321))),
        );
        let assignment = CStatement::Assign {
            name: "held".into(),
            expression: CExpression::Multiply(
                Box::new(CExpression::Variable("held".into())),
                Box::new(CExpression::Value(CValue::UInt32(
                    MachineTerm::uint32_constant(3),
                ))),
            ),
            source: Default::default(),
        };
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let outcome = super::super::super::statements::execute_c_statement(
                    &state,
                    &assignment,
                    &PureFactContext::new(),
                )
                .unwrap();
                let CStatementOutcome::Normal(after) = outcome else {
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
        let mut state = CState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "held",
            ExecutionValue::from(root.clone()),
            CType::UInt32,
            false,
            false,
            false,
            false,
        );
        let statement = CStatement::Return(CExpression::Variable("held".into()));
        let function = c_function(CType::UInt32, "handoff", Vec::new(), statement.clone());
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let CStatementOutcome::Return { value, .. } =
                    super::super::super::statements::execute_c_statement(
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
                    "received",
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
            let exports = KernelTermExport::machine_export_count();
            let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
                super::super::super::statements::execute_c_statement_paths(
                    &CState::new(),
                    &statement,
                    &PureFactContext::new(),
                    CExecutionContext::execute_bodies(&environment),
                    &mut ExecutionBudget::new(),
                )
                .unwrap()
            });
            let [path] = paths.as_slice() else {
                panic!("one complete machine path");
            };
            let CStatementOutcome::Return { value, state } = &path.outcome else {
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
