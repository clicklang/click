#[test]
fn rebased_wide_bounds_retain_cold_coordinate_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let base = Pointer {
            block: "wide_bound_scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut root = KernelTerm::variable(KernelType::C(ty.c_type()), Variable(1018502));
        for _ in 0..size {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let index = MachineOperandView::Shared(&root).retain(ty);
        let range = CMemoryRange::new_wide(
            Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Int64Scaled {
                    value: index.clone(),
                    byte_width: 8,
                    unsigned: true,
                },
            },
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1),
            8,
        );
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let ((first, last), work) = crate::instrumentation::measure_deterministic_work(|| {
            shared_rebased_wide_bounds(&range, &base, &facts).unwrap()
        });
        assert_eq!(first, index);
        let Some((found, op, [left, right])) = last.operand_view().binary() else {
            panic!("shared endpoint addition")
        };
        assert_eq!(found, ty);
        assert_eq!(op, MachineBinaryOp::Add);
        assert_eq!(left.retain(ty), index);
        assert_eq!(right.uint64_constant(), Some(1));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
