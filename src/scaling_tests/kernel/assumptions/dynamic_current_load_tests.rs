#[test]
fn memory_load_queries_retain_growing_shared_arithmetic() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, VerificationSession,
    };
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let memory = Memory::new().store(pointer(), ProgramValue::Int32((size as u32).into()));
        let other = memory
            .clone()
            .store(pointer(), ProgramValue::Int32(1u32.into()));
        let format = MachineIntegerType::Int32;
        let mut root = conversion_root(load_payload(&memory, format), format);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.clone(),
                        KernelTerm::variable(
                            KernelType::C(ProgramType::Int32),
                            Variable(996000 + index),
                        ),
                    ],
                );
                let term = observed(root.clone(), format);
                assert_eq!(
                    current_memory_loads_in_term(&term, &memory).unwrap(),
                    vec![(pointer(), 4)],
                    "size={size}, index={index}"
                );
                assert!(
                    current_memory_loads_in_term(&term, &other)
                        .unwrap()
                        .is_empty()
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
