use super::*;

#[test]
fn retained_literal_completion_keys_keep_exact_literals_and_skip_compound_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let literal = KernelTermImport::default().machine(format, &MachineTerm::uint32_constant(3));
        let mut root = literal.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [root, literal.clone()],
            );
        }
        let outcome = |root| CFunctionOutcome::Return {
            value: ExecutionValue::from(root).into(),
            state: Box::new(CState::new()),
        };
        let compound = outcome(root);
        let retained = outcome(literal);
        let native = CFunctionOutcome::Return {
            value: CValue::UInt32(MachineTerm::uint32_constant(3)).into(),
            state: Box::new(CState::new()),
        };
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            literal_completion_key(&retained),
            literal_completion_key(&native)
        );
        assert!(literal_completion_key(&retained).is_some());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert!(literal_completion_key(&compound).is_none());
            }
        });
        assert!(work <= size, "{size}: {work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
