#[test]
fn named_program_value_handoffs_retain_growing_dags_without_native_exports() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut previous = None;
    for size in [4, 16, 64, 256] {
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996936));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut values = ProgramValueBindings::new();
            values.insert_retained("result".into(), ExecutionValue::Shared(root.clone()));
            for _ in 0..32 {
                let values = values.clone();
                assert_eq!(values.get_retained("result").unwrap().root(), Some(&root));
            }
        });
        assert!(!root.has_cached_native_argument());
        if let Some(prior) = previous {
            assert_eq!(work, prior, "size={size}");
        }
        previous = Some(work);
    }
}
