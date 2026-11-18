#[test]
fn evaluated_sequence_handoffs_keep_growing_dags_without_exports() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let atom =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(10993406));
        let mut root = atom;
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let state =
            ExecutionState::new().with_retained_local("word", ExecutionValue::Shared(root.clone()));
        let expression = SpecSequenceExpression::Literal(vec![SpecExpression::ProgramExpression(
            ProgramExpression::Variable("word".into()),
        )]);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut execution = ExecutionBudget::default();
            let paths = evaluate_spec_sequence_at_state_in(
                SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
                &expression,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut execution),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            for _ in 0..32 {
                let sequence = paths[0].value.clone();
                let SequenceTermNode::Literal(values) = sequence.node.as_ref() else {
                    panic!("literal")
                };
                assert_eq!(values.retained_value(0).unwrap().shared(), Some(&root));
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
