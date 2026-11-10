#[test]
fn offset_reconstruction_retains_cold_and_growing_shared_indices() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::C(T::Int32.c_type()), Variable(1018210));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    T::Int32,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                let index = V::Shared(&root).retain(T::Int32);
                let offset = scaled(index.clone(), 4, false);
                assert_eq!(shared_element_index_from_offset(&offset, 4), Some(index));
                assert!(shared_byte_offset_from_pointer_offset(&offset).is_some());
                assert!(
                    PureFactContext::new().element_index_rebuild_is_exact_for_width(&offset, 4)
                );
                assert!(shared_element_index_from_offset(&offset, 8).is_none());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
