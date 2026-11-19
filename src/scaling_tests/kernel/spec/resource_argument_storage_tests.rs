#[test]
fn resource_argument_evaluation_and_description_handoffs_keep_growing_dags() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993605));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let state =
            ExecutionState::new().with_retained_local("word", ExecutionValue::Shared(root.clone()));
        let resource = SpecResource::Composite {
            name: "SharedArgument".into(),
            arguments: vec![SpecExpression::ProgramExpression(
                ProgramExpression::Variable("word".into()),
            )],
        };
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::default();
            let paths = evaluate_spec_resource_at_state_in(
                SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
                &resource,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            let Resource::Composite { arguments, .. } = &paths[0].0 else {
                panic!("composite")
            };
            let instance = ResourceInstance::new(
                InstanceId::from_variable(Variable(10993606)),
                "SharedArgument".into(),
                arguments.clone(),
                ResourceFieldSchema::new(vec![("marker".into(), ResourceFieldType::Integer)])
                    .unwrap(),
                vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(
                    10993607,
                )))]
                .into(),
            )
            .unwrap();
            for _ in 0..32 {
                let copy = instance.clone();
                let description = crate::kernel::ResourceDescription::from_instance(&copy);
                assert!(description.arguments().shares_storage_with(arguments));
                assert_eq!(
                    description.arguments().program_value(0).unwrap().shared(),
                    Some(&root)
                );
                let reference = crate::kernel::ResourceReference::from_instance(&copy);
                assert_eq!(
                    reference
                        .description()
                        .arguments()
                        .program_value(0)
                        .unwrap()
                        .shared(),
                    Some(&root)
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
