#[test]
fn retained_index_checks_scale_with_growing_prefixes_without_exports() {
    for capturing in [false, true] {
        let mut samples = vec![];
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let ty = MachineIntegerType::UInt64;
            let mut root = KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(994520));
            let context = PureFactContext::new();
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let run = || {
                    for _ in 0..size {
                        root = KernelTerm::machine_binary_shared(
                            ty,
                            MachineBinaryOp::Add,
                            [root.clone(), root],
                        );
                        let offset = wide(MachineOperandView::Shared(&root).retain(ty), 4);
                        assert_eq!(
                            wide_element_offsets_proven_distinct(
                                &offset,
                                &PointerOffsetTerm::Constant(0),
                                &context
                            ),
                            Some(false)
                        );
                    }
                };
                if capturing {
                    crate::kernel::assumptions::capture_implicit_reasoning_provenance(run);
                } else {
                    run();
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|p| p[1] <= 5 * p[0] + 100),
            "capture={capturing}: {samples:?}"
        );
    }
}
