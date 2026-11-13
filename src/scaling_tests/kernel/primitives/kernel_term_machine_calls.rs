use super::*;
#[test]
fn machine_call_roots_retain_growing_shared_arguments_without_exports() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut operand = KernelTerm::variable(KernelType::C(CType::Int32), Variable(995803));
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                operand = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [operand.clone(), operand],
                );
                let application = SharedPureApplication::intern(
                    "f".into(),
                    vec![PureFunctionArgument::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(format, operand.clone()).unwrap(),
                    )],
                );
                let root = KernelTermImport::default().machine_call(format, &application);
                assert_eq!(root.children()[0], operand, "prefix {index}");
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn common_call_numeric_identity_is_linear_cold_and_constant_warm() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root = KernelTerm::variable(KernelType::C(format.c_type()), Variable(995830));
        for _ in 0..size {
            root = KernelTerm::intern(
                KernelType::C(format.c_type()),
                KernelTermNode::Call {
                    name: "identity_chain".into(),
                    arguments: vec![root.clone(), root],
                },
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (identity, cold) = crate::instrumentation::measure_deterministic_work(|| {
            SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap()
        });
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap(),
                identity
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(matches!(root.node(), KernelTermNode::Call { .. }));
        samples.push((cold, warm));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].0 <= 5 * pair[0].0, "{samples:?}");
        assert_eq!(pair[1].1, pair[0].1, "{samples:?}");
    }
}
