#[test]
fn shared_address_queries_reuse_growing_index_dags() {
    use crate::kernel::{KernelTerm, MachineBinaryOp};
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let graph = EqualityGraph::default();
        let base = Pointer::symbolic(Variable(991411));
        let ty = MachineIntegerType::Int32;
        let mut root = KernelTermImport::default()
            .machine_arithmetic(ty, &MachineTerm::Variable(Variable(991412)))
            .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Multiply,
                    [root.clone(), root.clone()],
                );
                let class = graph
                    .indexed_address_class(&base, V::Shared(&root), false, 4)
                    .unwrap();
                let different = graph
                    .indexed_address_class(&base.offset_by_bytes(1), V::Shared(&root), false, 4)
                    .unwrap();
                assert_ne!(
                    graph.address_class_root(class),
                    graph.address_class_root(different)
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 5, "{samples:?}");
    }
}
