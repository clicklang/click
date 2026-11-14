#[test]
fn mixed_operation_construction_does_not_walk_shared_operand_dags() {
    for reverse in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let ty = MachineIntegerType::Int32;
            let mut root =
                KernelTerm::variable(KernelType::Program(ty.c_type()), Variable(1007020));
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    ty,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let shared = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
            let native = SharedMachineIntegerTerm::intern(ty, opaque());
            let (left, right) = if reverse {
                (&native, &shared)
            } else {
                (&shared, &native)
            };
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                operation_observation(ty, Operation::Subtract, left, right).unwrap()
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let IntegerTerm::Machine(result) = result else {
                panic!("observation")
            };
            let KernelTermNode::MachineBinary { arguments, .. } =
                result.shared_operand().unwrap().node()
            else {
                panic!("operation")
            };
            assert_eq!(arguments[usize::from(reverse)], root);
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{reverse}: {samples:?}"
        );
    }
}
