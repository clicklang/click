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
            KernelType::Program(MachineIntegerType::Int32.c_type()),
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

#[test]
fn wide_coordinate_reconstruction_retains_cold_index_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let base = Pointer {
            block: "wide_shared_indices".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut root = KernelTerm::variable(
            KernelType::Program(MachineIntegerType::UInt64.c_type()),
            Variable(1018321),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let index = MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64);
        let pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Int64Scaled {
                value: index.clone(),
                byte_width: 8,
                unsigned: true,
            },
        };
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                pointer.shared_wide_element_index_from_base(&base, 8),
                Some(index.clone())
            );
            assert_eq!(
                facts.shared_wide_element_index_of_access(&pointer, &base, 8),
                Some(index)
            );
            assert!(
                facts
                    .shared_wide_element_index_of_access(&pointer, &base, 4)
                    .is_none()
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
