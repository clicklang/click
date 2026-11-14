#[test]
fn typed_offset_evidence_refuses_cold_arithmetic_without_exports() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut left = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(1018821));
        let mut right = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(1018822));
        for _ in 0..size {
            left =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [left.clone(), left]);
            right =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [right.clone(), right]);
        }
        let offset = |root: &KernelTerm| PointerOffsetTerm::Int32Scaled {
            value: MachineOperandView::Shared(root).retain(ty),
            byte_width: 4,
        };
        let (left, right) = (offset(&left), offset(&right));
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_offset_equality_evidence(&left, &right, &facts)
        });
        assert!(answer.is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
