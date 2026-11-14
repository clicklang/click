#[test]
fn shared_checking_simplification_visits_dag_nodes_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            crate::kernel::KernelType::Program(T::Int32.c_type()),
            Variable(1017111),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(T::Int32, B::Multiply, [root.clone(), root]);
        }
        let facts = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.simplify_machine_operand_under_assumptions(V::Shared(&root), T::Int32)
        });
        assert_eq!(
            result.operand_view().retain(T::Int32),
            V::Shared(&root).retain(T::Int32)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
