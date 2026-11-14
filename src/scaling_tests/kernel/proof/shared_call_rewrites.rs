#[test]
fn common_call_rewrite_visits_shared_arguments_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(995870));
        for _ in 0..size {
            let child = call(format, root);
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [child.clone(), child],
            );
        }
        let from = MachineTerm::Variable(Variable(995870));
        let to = MachineTerm::Variable(Variable(995871));
        let exports = KernelTermExport::machine_export_count();
        let mut rewrite = TermRewrite::for_bits_checked(&from, &to);
        let (result, cold) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite.shared_machine_operand(&root).unwrap()
        });
        assert_eq!(rewrite.refusal(), None);
        assert_ne!(result, root);
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(rewrite.shared_machine_operand(&root), Some(result.clone()))
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((cold, warm));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].0 <= 5 * pair[0].0, "{samples:?}");
        assert_eq!(pair[1].1, pair[0].1, "{samples:?}");
    }
}
