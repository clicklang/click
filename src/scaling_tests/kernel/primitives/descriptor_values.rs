#[test]
fn protocol_descriptors_keep_growing_shared_values_and_condition_dags() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut word =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993645));
        let mut condition = KernelTerm::variable(KernelType::Bool, Variable(10993646));
        for _ in 0..size {
            word = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [word.clone(), word],
            );
            condition = KernelTerm::boolean_equal_raw([condition.clone(), condition]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let observed = StoredProgramValue::from(ExecutionValue::Shared(word.clone()));
            let held = StoredConditionTerm::from_root(condition.clone()).unwrap();
            let address = Address::symbolic(Variable(10993647));
            let mut right = PublicationRight::new(
                PublicationSide::Subscriber,
                address.clone(),
                crate::kernel::ResourceDescription::new(
                    "payload".into(),
                    vec![].into(),
                    ResourceFieldSchema::new(vec![]).unwrap(),
                ),
            );
            right.observed = Some(observed);
            let guard = ConditionalMutexGuard {
                identity: Variable(10993648),
                guard: MutexIdentity {
                    epoch: Some(1),
                    mutex: address.clone(),
                },
                initialization: MutexIdentity {
                    epoch: Some(2),
                    mutex: address,
                },
                held,
            };
            for _ in 0..32 {
                let copy = right.clone();
                assert_eq!(copy.observed.as_ref().unwrap().root(), Some(&word));
                let copy = guard.clone();
                assert_eq!(copy.held.root(), Some(&condition));
                assert_eq!(copy.identity, guard.identity);
                assert_eq!(copy.guard, guard.guard);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!word.has_cached_native_argument());
        assert!(!condition.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
