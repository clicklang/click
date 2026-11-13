use super::*;

#[test]
fn retained_contract_result_storage_and_exit_memory_skip_expression_prefixes() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(998340)));
        let three = KernelTermImport::default().machine(format, &MachineTerm::uint32_constant(3));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [root, three.clone()],
            );
        }
        let value = StoredExecutionValue::from(ExecutionValue::from(root.clone()));
        let function = c_function(
            CType::UInt32,
            "result",
            Vec::new(),
            c_return(c_uint32_literal(0)),
        );
        let mut state = CState::new();
        let caller = CState::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                set_function_result(&mut state, &function, value.clone());
                let memory = function_exit_memory(&caller, &state, &value, &function);
                assert_eq!(&memory, state.memory());
            }
        });
        assert_eq!(
            state.locals.get(C_CONTRACT_RESULT_NAME).unwrap().shared(),
            Some(&root)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert_eq!(work, [0, 0, 0], "no expression traversal at these handoffs");
}
