use super::*;

#[test]
fn overflow_conditions_reuse_shared_numeric_dags() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut operand =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999901));
        for _ in 0..size {
            operand = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [operand.clone(), operand],
            );
        }
        let source = KernelTerm::boolean_overflow_raw(
            format,
            OverflowOperation::Add,
            [operand.clone(), operand],
        );
        let nested = KernelTerm::boolean_equal_raw([
            source.clone(),
            KernelTerm::intern(KernelType::Bool, KernelTermNode::BoolLiteral(false)),
        ]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                    &source,
                    Variable(999902),
                    &MachineTerm::constant(1)
                ),
                Some(source.clone())
            );
            assert_eq!(
                crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                    &nested,
                    Variable(999902),
                    &Pointer::null()
                ),
                Some(nested)
            );
            assert_eq!(
                crate::kernel::memory_provenance::transport_framed_common_condition(
                    &source,
                    &crate::kernel::Memory::new(),
                    None
                ),
                Some(source)
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 200 * size + 2000, "size={size}, work={work}");
    }
}
