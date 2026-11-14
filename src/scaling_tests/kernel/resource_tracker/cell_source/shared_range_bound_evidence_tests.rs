use super::*;

#[test]
fn growing_shared_range_certificates_reuse_endpoints_without_exports() {
    let measure = |count| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable =
            |n| KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(n));
        let mut root = variable(1_000_200);
        let mut facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root.clone(), variable(1_000_201 + index)],
                );
                let observation =
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let condition = ConditionTerm::integer_less_equal(
                    IntegerTerm::Machine(observation.clone()),
                    IntegerTerm::constant_i64(7),
                );
                facts = facts.assume_proposition(Proposition::ConditionIs(condition.clone(), true));
                let evidence = RangeBoundEvidence::for_true_condition(&condition, &facts).unwrap();
                assert!(evidence.checks(&condition, &facts));
                assert!(!observation.has_boxed_operand());
                assert_eq!(
                    facts.execution_variable_ceiling(),
                    Some(Variable(1_000_201 + index))
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work
    };
    let small = measure(32);
    let large = measure(128);
    assert!(
        large <= small * 5 + 100,
        "range evidence work grew from {small} to {large}"
    );
}
