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
