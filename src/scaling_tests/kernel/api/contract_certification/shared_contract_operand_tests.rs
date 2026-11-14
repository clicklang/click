#[test]
fn shared_contract_scope_walk_visits_dag_nodes_once() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(1017141);
        let mut root = KernelTerm::variable(
            crate::kernel::KernelType::Program(crate::kernel::ProgramType::Int32),
            variable,
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Multiply,
                [root.clone(), root],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            collect_shallow_operand_variables(Operand::Shared(&root), &mut variables);
            variables
        });
        assert_eq!(variables, BTreeSet::from([variable]));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}
