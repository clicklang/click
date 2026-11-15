use super::*;
#[test]
fn boolean_composition_and_casts_keep_growing_prefixes_shared() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut value = KernelTerm::variable(KernelType::Bool, Variable(999430));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let guard = KernelTerm::variable(KernelType::Bool, Variable(999431 + index as u64));
                value = KernelTerm::boolean_if([guard.clone(), value, guard]);
                let cast = KernelTerm::boolean_cast(MachineIntegerType::Int32, value.clone());
                let KernelTermNode::BoolCast { operand, .. } = cast.node() else {
                    panic!();
                };
                assert_eq!(operand, &value);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 50 * size + 100, "size={size}, work={work}");
    }
}
