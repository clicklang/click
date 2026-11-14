#[test]
fn intrinsic_format_queries_retain_growing_shared_prefixes() {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, VerificationSession};
    let mut samples = Vec::new();
    for count in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(994201));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..count {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(
                            KernelType::Program(ProgramType::Int32),
                            Variable(994202 + index),
                        ),
                    ],
                );
                let value: SharedIntegerTerm = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap(),
                )
                .into();
                let proposition = Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(
                        value,
                        IntegerTerm::constant_i64(i64::from(i32::MAX)).into(),
                    ),
                    true,
                );
                assert!(holds_by_format_range(&proposition));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
