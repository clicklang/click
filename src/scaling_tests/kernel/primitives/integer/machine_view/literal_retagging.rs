#[test]
fn literal_retagging_ignores_neighboring_terms_and_shared_parents() {
    use crate::kernel::{KernelTermExport, MachineBinaryOp};
    use MachineIntegerType::{Int64, UInt64};
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let literal = KernelTermImport::default()
            .machine(UInt64, &MachineTerm::uint64_constant(u64::MAX - 6));
        let mut related = KernelTermImport::default()
            .machine(UInt64, &MachineTerm::Variable(Variable(1_990_000)));
        let guard = KernelTermImport::default().condition(&ConditionTerm::Constant(true));
        let mut conditional = literal.clone();
        let mut unrelated = Vec::new();
        for index in 0..size {
            unrelated.push(
                KernelTermImport::default()
                    .machine(UInt64, &MachineTerm::Variable(Variable(1_991_000 + index))),
            );
            related = KernelTerm::machine_binary_shared(
                UInt64,
                MachineBinaryOp::Add,
                [related, literal.clone()],
            );
            conditional = KernelTerm::machine_if_shared(
                UInt64,
                [guard.clone(), conditional.clone(), conditional],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
            let signed = literal.with_machine_observation_type(Int64);
            MachineOperandView::Shared(&signed).observe(Int64)
        });
        assert_eq!(observed, Some(IntegerTerm::constant((-7).into())));
        let (signed, conditional_work) = crate::instrumentation::measure_deterministic_work(|| {
            conditional.with_machine_observation_type(Int64)
        });
        assert!(conditional_work <= 3 * (size + 1) as usize);
        let mut leaf = signed.clone();
        for _ in 0..size {
            let KernelTermNode::MachineIf { arguments } = leaf.node() else {
                panic!("conditional structure must remain shared");
            };
            assert_eq!(arguments[1].id(), arguments[2].id());
            leaf = arguments[1].clone();
        }
        assert_eq!(
            MachineOperandView::Shared(&leaf).observe(Int64),
            Some(IntegerTerm::constant((-7).into())),
        );
        let (repeated, repeated_work) = crate::instrumentation::measure_deterministic_work(|| {
            conditional.with_machine_observation_type(Int64)
        });
        assert_eq!(repeated.id(), signed.id());
        assert_eq!(repeated_work, 0);
        assert_eq!(signed.with_machine_observation_type(UInt64), conditional);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(unrelated.len(), size as usize);
        assert!(matches!(
            related.node(),
            KernelTermNode::MachineBinary { .. }
        ));
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}
