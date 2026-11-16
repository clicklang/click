#[test]
fn signed_literal_domain_reading_ignores_unrelated_terms_and_parents() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let literal = KernelTermImport::default().machine(
            MachineIntegerType::Int64,
            &MachineTerm::uint64_constant(u64::MAX - 6),
        );
        let variable = MachineTerm::Variable(Variable(1_991_000));
        let mut parent = literal.clone();
        let mut unrelated = Vec::new();
        for index in 0..size {
            unrelated.push(KernelTermImport::default().machine(
                MachineIntegerType::Int64,
                &MachineTerm::Variable(Variable(1_992_000 + index)),
            ));
            parent = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int64,
                MachineBinaryOp::Add,
                [parent, literal.clone()],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (domain, work) = crate::instrumentation::measure_deterministic_work(|| {
            Proposition::signed_arithmetic_domain_views(
                MachineIntegerType::Int64,
                MachineBinaryOp::Add,
                MachineOperandView::Shared(&literal),
                MachineOperandView::Legacy(&variable),
            )
        });
        assert_eq!(
            domain,
            Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int64,
                MachineBinaryOp::Add,
                &MachineTerm::int64_constant(-7),
                &variable,
            )
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(unrelated.len(), size as usize);
        assert!(matches!(
            parent.node(),
            KernelTermNode::MachineBinary { .. }
        ));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}
