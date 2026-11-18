#[test]
fn call_argument_paths_retain_shared_prefixes_without_exporting() {
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998700));
        for _ in 0..depth {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let mut values: crate::persistent::PersistentMap<
            crate::kernel::BindingName,
            crate::kernel::KernelTerm,
        > = crate::persistent::PersistentMap::default();
        values.insert("x".into(), root.clone());
        let state = ExecutionState::new();
        let scope = SpecScope {
            values: Some(&values),
            ..SpecScope::unbound(&state, None)
        };
        let argument = SpecPureFunctionArgument::Value(SpecExpression::ProgramExpression(
            ProgramExpression::Variable("x".into()),
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
                ProgramType::UInt32,
                None,
                None,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        let SpecValue::Shared(value) = &calls[0].value else {
            panic!("expected a common scalar call");
        };
        assert!(matches!(value.node(), KernelTermNode::Call { .. }));
        assert_eq!(value.children(), &[root.clone()]);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 128, "scalar call at depth {depth}: {work} work");

        // The declared pointer origin selects only argument 1. Determining a
        // null result must not materialize the unrelated exponential DAG.
        let null = ProgramValue::Pointer(Pointer::new(Address::null(), ProgramType::Int32Pointer));
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
                ProgramType::Int32Pointer,
                Some(&origins),
                None,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
        });
        assert_eq!(results.len(), 1);
        assert!(matches!(
            results[0].value.shared().unwrap().node(),
            KernelTermNode::Pointer(_)
        ));
        assert_eq!(results[0].value.clone().into_native(), null);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 128, "selected origin at depth {depth}: {work} work");
    }
}

#[test]
fn retained_constant_call_arguments_keep_existing_decision_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let scope = SpecScope::unbound(&state, None);
    let argument = SpecPureFunctionArgument::Value(SpecExpression::Subtract(
        Box::new(SpecExpression::Value(ProgramValue::Int32(
            MachineTerm::constant(2),
        ))),
        Box::new(SpecExpression::Value(ProgramValue::Int32(
            MachineTerm::constant(1),
        ))),
    ));
    let mut execution = ExecutionBudget::new();
    let calls = evaluate_spec_pure_function_application_paths_in(
        scope,
        "retained_steps",
        &[argument],
        ProgramType::Int32,
        None,
        None,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut execution),
    )
    .unwrap();
    let SpecValue::Shared(root) = &calls[0].value else {
        panic!("scalar call");
    };
    let produced = root.machine_conversion_leaf().unwrap();
    let native = MachineTerm::ClickFunctionApplication {
        name: "retained_steps".into(),
        arguments: vec![PureFunctionArgument::Value(ProgramValue::Int32(
            MachineTerm::constant(1),
        ))],
    };
    let MachineTerm::ClickFunctionApplication { arguments, .. } = produced else {
        panic!("call");
    };
    let expected = PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::constant(1)));
    assert_eq!(
        arguments[0].machine_identity(),
        expected.machine_identity(),
        "produced: {arguments:?}"
    );
    let known = ConditionTerm::equal(native, MachineTerm::constant(0));
    let required = ConditionTerm::equal(produced.clone(), MachineTerm::constant(0));
    let proof_facts =
        crate::kernel::proof::PureFactStore::from_ordered(&[Proposition::condition_is(
            known.clone(),
            true,
        )]);
    assert!(
        proof_facts.introduced_goal_available(&Proposition::condition_is(required.clone(), true))
    );
    let facts = PureFactContext::new().assume_condition(known, true);
    assert_eq!(facts.decide(&required), Some(true));
}

#[test]
fn mixed_typed_call_arguments_keep_growing_roots_without_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = TypeParameterName::intern("MixedGrowingT").algebraic_type();
        let mut algebraic =
            KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(1008503));
        let mut float =
            KernelTerm::variable(KernelType::Program(ProgramType::Float64), Variable(1008504));
        for _ in 0..size {
            algebraic = KernelTerm::algebraic_call(
                ty.clone(),
                "grow".into(),
                vec![(algebraic.clone(), None), (algebraic, None)],
            );
            float = KernelTerm::float_call(
                KernelFloatType::Float64,
                "grow_float".into(),
                vec![(float.clone(), None), (float, None)],
            );
        }
        let float_exports = KernelTermExport::float_export_count();
        let algebraic_exports = KernelTermExport::algebraic_export_count();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let arguments = [algebraic.clone(), float.clone()]
                .into_iter()
                .map(|root| {
                    SpecCallArgument::from_value(SpecValue::Shared(root)).into_typed_call_operand()
                })
                .collect();
            let call = KernelTerm::float_call(KernelFloatType::Float64, "mixed".into(), arguments);
            let KernelTermNode::ProgramParameter { operand } = call.children()[0].node() else {
                panic!("program argument form");
            };
            assert_eq!(operand, &algebraic);
            assert_eq!(&call.children()[1], &float);
        });
        assert!(work < 128, "size={size} work={work}");
        assert_eq!(KernelTermExport::float_export_count(), float_exports);
        assert_eq!(
            KernelTermExport::algebraic_export_count(),
            algebraic_exports
        );
    }
}
