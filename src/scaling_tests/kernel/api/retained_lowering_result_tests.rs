#[test]
fn common_lowering_capture_keeps_growing_arithmetic_shared() {
    for size in [8, 32, 128] {
        let _session = VerificationSession::enter();
        let mut expression = SpecExpression::Value(ProgramValue::UInt32(OldMachineTerm::Variable(
            Variable(999994),
        )));
        for _ in 0..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::UInt32(
                    OldMachineTerm::uint32_constant(1),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            program_evaluate_retained_spec_expression(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
            )
        });
        let result = result.unwrap();
        assert_eq!(result.value.ty(), &KernelType::Program(ProgramType::UInt32));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 1000 * size + 1000, "size={size}, work={work}");
    }
}
