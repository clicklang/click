#[test]
fn signed_literal_domain_reading_ignores_unrelated_terms_and_parents() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let literal = KernelTermImport::default().machine(
            MachineIntegerType::Int64,
            &OldMachineTerm::uint64_constant(u64::MAX - 6),
        );
        let variable = OldMachineTerm::Variable(Variable(1_991_000));
        let mut parent = literal.clone();
        let mut unrelated = Vec::new();
        for index in 0..size {
            unrelated.push(KernelTermImport::default().machine(
                MachineIntegerType::Int64,
                &OldMachineTerm::Variable(Variable(1_992_000 + index)),
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
                MachineOperandView::Old(&variable),
            )
        });
        assert_eq!(
            domain,
            Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int64,
                MachineBinaryOp::Add,
                &OldMachineTerm::int64_constant(-7),
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

#[test]
fn domain_construction_preserves_closed_shared_conditions_without_export() {
    use crate::kernel::{KernelTerm, StoredConditionTerm};
    for depth in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::boolean_literal(true);
        for _ in 0..depth {
            root = KernelTerm::boolean_equal_raw([root.clone(), root]);
        }
        for expected in [false, true] {
            let condition = StoredConditionTerm::from_root(root.clone()).unwrap();
            let claim = Proposition::condition_is(condition, expected);
            let (domain, work) = crate::instrumentation::measure_deterministic_work(|| {
                Proposition::arithmetic_domain([claim.clone()])
            });
            assert_eq!(domain, Some(claim));
            assert!(!root.has_cached_native_argument());
            assert_eq!(work, 1);
        }
    }
}
