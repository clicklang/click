#[test]
fn shared_comparison_growing_prefixes_scale_linearly() {
    let measure = |count| {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = |n| KernelTerm::variable(KernelType::C(CType::Int32), Variable(n));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut root = variable(993000);
            for index in 0..count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Multiply,
                    [root, variable(993001 + index)],
                );
                let condition = Proposition::ConditionIs(
                    ConditionTerm::integer_less_equal(
                        IntegerTerm::Machine(
                            SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                        ),
                        IntegerTerm::constant_i64(7),
                    ),
                    true,
                );
                assert!(TermRewrite::arithmetic_comparison(&condition).is_none());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work
    };
    let small = measure(64);
    let large = measure(256);
    assert!(
        large <= small * 5,
        "prefix reconstruction grew from {small} to {large}"
    );
}
