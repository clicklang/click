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

#[test]
fn proposition_outcome_handoffs_retain_growing_machine_and_float_operands() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut word =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993664));
        let mut float = KernelTerm::variable(
            KernelType::Program(ProgramType::Float32),
            Variable(10993665),
        );
        for _ in 0..size {
            word = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [word.clone(), word],
            );
            float = KernelTerm::float_negate(KernelFloatType::Float32, float).unwrap();
        }
        let state = ExecutionState::new().with_retained_local("result", word.clone().into());
        let pointer = Address::symbolic(Variable(10993666));
        let memory = SymbolicMemory::new().store_retained(pointer.clone(), float.clone().into());
        let exports = (
            KernelTermExport::machine_export_count(),
            KernelTermExport::float_export_count(),
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let expression = crate::kernel::prove_program_expression_evaluation(
                state,
                ProgramExpression::Variable("result".into()),
            )
            .unwrap();
            let load = crate::kernel::prove_memory_load(memory, pointer);
            for _ in 0..32 {
                let expression = expression.proposition().clone();
                let Proposition::ProgramExpressionEvaluates {
                    outcome: ExpressionOutcome::Value(value),
                    ..
                } = expression
                else {
                    panic!("expression value");
                };
                assert_eq!(value.root(), Some(&word));
                let load = load.proposition().clone();
                let Proposition::MemoryLoads {
                    outcome: ExpressionOutcome::Value(value),
                    ..
                } = load
                else {
                    panic!("load value");
                };
                assert_eq!(value.root(), Some(&float));
            }
        });
        assert_eq!(
            (
                KernelTermExport::machine_export_count(),
                KernelTermExport::float_export_count()
            ),
            exports
        );
        assert!(!word.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}

#[test]
fn loadability_count_storage_shares_growing_machine_operands() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let mut root = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(10993683),
            );
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root],
                );
            }
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let fact = Proposition::MemoryLoadable {
                    memory: SymbolicMemory::new(),
                    base: Address::symbolic(Variable(10993684)),
                    bytes: StoredMachineTerm::from_value(root.clone().into()).unwrap(),
                    wide: format == MachineIntegerType::UInt64,
                };
                for _ in 0..32 {
                    let Proposition::MemoryLoadable { bytes, .. } = fact.clone() else {
                        unreachable!()
                    };
                    assert_eq!(bytes.root(), Some(&root));
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "size={size} format={format:?}"
            );
        }
    }
}

#[test]
fn condition_proposition_storage_clones_growing_logical_dags_without_exports() {
    let mut baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(10993715));
        for _ in 0..size {
            root = KernelTerm::boolean_equal_raw([root.clone(), root]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let proposition = Proposition::condition_is(
                StoredConditionTerm::from_root(root.clone()).unwrap(),
                false,
            );
            for _ in 0..32 {
                let Proposition::ConditionIs(value, truth) = proposition.clone() else {
                    unreachable!();
                };
                assert_eq!(value.root(), Some(&root));
                assert!(!truth);
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        assert_eq!(work, *baseline.get_or_insert(work), "size={size}");
    }
}
