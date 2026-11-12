#[test]
fn call_argument_paths_retain_shared_prefixes_without_exporting() {
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root = KernelTerm::variable(KernelType::C(CType::UInt32), Variable(998700));
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let mut values = crate::persistent::PersistentMap::default();
        values.insert("x".to_string(), root.clone());
        let state = CState::new();
        let scope = SpecScope {
            values: Some(&values),
            ..SpecScope::unbound(&state, None)
        };
        let argument = SpecPureFunctionArgument::Value(SpecExpression::CExpression(
            CExpression::Variable("x".into()),
        ));
        let exports = KernelTermExport::machine_export_count();
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::new();
            evaluate_spec_pure_function_argument_paths_in(
                scope,
                &argument,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value, SpecCallArgument::Shared(root.clone()));
        assert!(paths[0].facts.is_empty());
        assert!(paths[0].obligations.is_empty());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 64, "argument depth {depth}: {work} work");

        // An actual scalar call must retain the exact argument DAG in its
        // payload, not just while assembling the argument paths.
        let mut execution = ExecutionBudget::new();
        let (calls, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_pure_function_application_paths_in(
                scope,
                "retained_argument",
                std::slice::from_ref(&argument),
                CType::UInt32,
                None,
                None,
                None,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        let SpecValue::Native(CValue::UInt32(MachineTerm::ClickFunctionApplication {
            arguments,
            ..
        })) = &calls[0].value else {
            panic!("expected a scalar call payload");
        };
        let [PureFunctionArgument::SharedMachine(value)] = arguments.as_slice() else {
            panic!("expected a retained call argument");
        };
        assert_eq!(value.shared_operand(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 128, "scalar call at depth {depth}: {work} work");

        // The declared pointer origin selects only argument 1. Determining a
        // null result must not materialize the unrelated exponential DAG.
        let null = CValue::Pointer(CPointerValue::new(Pointer::null(), CType::Int32Pointer));
        let arguments = [
            argument,
            SpecPureFunctionArgument::Value(SpecExpression::Value(null.clone())),
        ];
        let origins = PurePointerResult {
            classes: BTreeSet::new(),
            arguments: [1].into_iter().collect(),
        };
        let mut execution = ExecutionBudget::new();
        let (results, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_pure_function_application_paths_in(
                scope,
                "selected_origin",
                &arguments,
                CType::Int32Pointer,
                Some(&origins),
                None,
                None,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].value, SpecValue::Native(null));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 128, "selected origin at depth {depth}: {work} work");
    }
}
