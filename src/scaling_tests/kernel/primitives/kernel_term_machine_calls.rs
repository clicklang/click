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
