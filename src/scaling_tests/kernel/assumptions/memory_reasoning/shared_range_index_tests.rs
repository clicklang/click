#[test]
fn retained_delta_and_affine_queries_scale_with_the_selected_dag() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let base = Pointer {
            block: "shared_delta_scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut root = KernelTerm::variable(
            KernelType::C(MachineIntegerType::Int32.c_type()),
            Variable(1018310),
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Subtract,
                    [root.clone(), root.clone()],
                );
                let index = MachineOperandView::Shared(&root).retain(MachineIntegerType::Int32);
                let pointer = base.offset_by_shared_elements(index.clone(), 4);
                let delta = pointer
                    .exact_element_delta_from_base(&base, 4, None)
                    .unwrap();
                assert_eq!(delta.index, index);
                assert_eq!(delta.as_index_term(), Some(index));
            }
            assert_eq!(
                affine_bitvector_difference_constant_views(
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Legacy(&MachineTerm::constant(0))
                ),
                Some(0)
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
