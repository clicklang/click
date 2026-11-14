#[test]
fn individual_order_steps_keep_growing_shared_endpoints() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(995211));
        let upper = MachineTerm::constant(100);
        let mut facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                let source = Proposition::ConditionIs(
                    ConditionTerm::integer_less_than(
                        observed(root.clone()),
                        IntegerTerm::constant_i64(100),
                    ),
                    true,
                );
                facts = facts
                    .assume_condition(
                        ConditionTerm::signed_less_equal(
                            0u32.into(),
                            MachineTerm::Variable(Variable(996000 + index)),
                        ),
                        true,
                    )
                    .assume_proposition(source.clone());
                let step = facts
                    .exact_direct_operand_order_step(
                        MachineOperandView::Shared(&root),
                        MachineOperandView::Legacy(&upper),
                        true,
                    )
                    .unwrap();
                assert_eq!(step.premise(), &source);
                assert!(facts.checks_exact_order_step(&step));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
