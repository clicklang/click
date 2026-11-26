#[test]
fn cold_offset_evidence_misses_do_not_export_shared_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut left =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1008120));
        let mut right =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1008121));
        for _ in 0..size {
            left = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Multiply,
                [left.clone(), left],
            );
            right = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Multiply,
                [right.clone(), right],
            );
        }
        let wrap = |root| {
            AddressOffset::int32_scaled(SharedMachineIntegerTerm::from_shared(ty, root).unwrap(), 4)
        };
        let (left, right) = (wrap(left), wrap(right));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                PureFactContext::new()
                    .pointer_offset_congruence_evidence(&left.clone(), &right.clone())
                    .is_none()
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
fn shared_offset_source_paths_scale_with_selected_dags() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let mut left =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1008140));
        let mut right =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1008141));
        for _ in 0..size {
            left = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Multiply,
                [left.clone(), left],
            );
            right = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Multiply,
                [right.clone(), right],
            );
        }
        let l = SharedMachineIntegerTerm::from_shared(ty, left).unwrap();
        let r = SharedMachineIntegerTerm::from_shared(ty, right).unwrap();
        let source = OldConditionTerm::IntegerEqual(
            crate::kernel::IntegerTerm::Machine(l.clone()).into(),
            crate::kernel::IntegerTerm::Machine(r.clone()).into(),
        );
        let a = AddressOffset::int32_scaled(l, 4);
        let b = AddressOffset::int32_scaled(r, 4);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let empty = PureFactContext::new();
            let facts = empty.clone().assume_condition(source, true);
            let proof = facts
                .pointer_offset_congruence_evidence(&a.clone(), &b.clone())
                .expect("shared source path");
            assert!(proof.checks(&a.clone(), &b.clone(), &facts));
            assert!(!proof.checks(&a.clone(), &b.clone(), &empty));
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
