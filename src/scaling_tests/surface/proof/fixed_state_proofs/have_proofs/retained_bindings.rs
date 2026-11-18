#[test]
fn selected_local_environment_handoffs_ignore_unrelated_values_and_dag_depth() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996942));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let mut state = ExecutionState::new()
            .with_retained_local("chosen", ExecutionValue::Shared(root.clone()));
        for index in 0..size {
            state = state.with_local(
                format!("unrelated_{index}"),
                crate::kernel::int32(index as u32),
            );
        }
        let names = BTreeSet::from(["chosen".to_string()]);
        let ((values, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::surface::lowering::contract_environment_for_names(
                ParameterBinding::default(),
                &names,
                &state,
            )
            .unwrap()
        });
        assert_eq!(values.get_retained("chosen").unwrap().root(), Some(&root));
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
        let (all, _) = crate::surface::lowering::contract_environment_at_state(
            &ProgramValueBindings::new(),
            &ClickArrayRefs::new(),
            &state,
        );
        assert_eq!(all.get_retained("chosen").unwrap().root(), Some(&root));
        assert!(!root.has_cached_native_argument());
    }
}
