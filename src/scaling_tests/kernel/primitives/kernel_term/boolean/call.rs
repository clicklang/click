use super::*;

#[test]
fn boolean_calls_keep_shared_arguments_across_selected_native_readings() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut operand =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(999410));
        for _ in 0..size {
            operand = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [operand.clone(), operand],
            );
        }
        let application = SharedPureApplication::intern(
            "boolean_shared_argument".into(),
            vec![PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, operand.clone())
                    .unwrap(),
            )],
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let root = KernelTermImport::default().boolean_call(&application);
            let KernelTermNode::Call { arguments, .. } = root.node() else {
                panic!();
            };
            assert_eq!(arguments[0], operand);
            for _ in 0..size {
                let ConditionTerm::BoolApplication(native) = root.boolean_call_native().unwrap()
                else {
                    panic!();
                };
                let PureFunctionArgument::SharedMachine(value) = &native.arguments()[0] else {
                    panic!();
                };
                assert_eq!(value.shared_operand(), Some(&operand));
            }
            assert_eq!(
                crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                    &root,
                    Variable(999411),
                    &MachineTerm::constant(1)
                ),
                Some(root.clone())
            );
            assert_eq!(
                crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                    &root,
                    Variable(999411),
                    &Pointer::null()
                ),
                Some(root)
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 200 * size + 2000, "size={size}, work={work}");
    }
}

#[test]
fn nested_boolean_argument_handoffs_retain_linear_shared_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(999550));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let application = SharedPureApplication::intern(
                    "nested_bool".into(),
                    vec![root.boolean_argument_native().unwrap().clone()],
                );
                let next = KernelTermImport::default()
                    .boolean_call_with_retained(&application, &[Some(root.clone())]);
                let KernelTermNode::Call { arguments, .. } = next.node() else {
                    panic!()
                };
                assert_eq!(arguments, &[root]);
                root = next;
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 100, "size={size}, work={work}");
    }
}
