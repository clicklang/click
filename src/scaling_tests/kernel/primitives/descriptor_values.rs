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
                identity: InstanceId::from_variable(Variable(10993648)),
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

#[test]
fn condition_hash_reuses_the_key_of_a_growing_shared_dag() {
    use std::hash::{DefaultHasher, Hash, Hasher};

    let mut warm_baseline = None;
    for size in [4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(KernelType::Bool, Variable(10993717));
        for _ in 0..size {
            root = KernelTerm::boolean_equal_raw([root.clone(), root]);
        }
        let condition = StoredConditionTerm::from_root(root.clone()).unwrap();
        let hash = || {
            let mut hasher = DefaultHasher::new();
            condition.hash(&mut hasher);
            hasher.finish()
        };
        let (fingerprint, cold_work) = crate::instrumentation::measure_deterministic_work(hash);
        assert!(cold_work <= 4 * (size + 1), "size={size} work={cold_work}");
        let (_, warm_work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                assert_eq!(hash(), fingerprint);
            }
        });
        assert_eq!(warm_work, *warm_baseline.get_or_insert(warm_work), "size={size}");
        assert!(!root.has_cached_native_argument());
    }
}

#[test]
fn mixed_integer_descriptor_identity_survives_handle_drop_without_exports() {
    use crate::kernel::{KernelFold, KernelFoldIndex, SharedMachineIntegerTerm};
    let format = MachineIntegerType::Int32;
    let variable = Variable(10993710);
    let guard = Variable(10993711);
    let make_observation = |format| {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            format,
            MachineTerm::Variable(variable),
        ))
    };
    let mut measured = Vec::new();
    for depth in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = make_observation(format);
        let leaf = KernelTermImport::default().integer(&source.into());
        let distinct = KernelTermImport::default()
            .integer(&make_observation(MachineIntegerType::UInt32).into());
        let zero = KernelTerm::integer_literal(0.into());
        let wrap = |body: KernelTerm| {
            let condition = KernelTerm::variable(KernelType::Bool, guard);
            let body = KernelTerm::integer_if_raw([condition, body, zero.clone()]);
            KernelFold::new(
                KernelFoldIndex::Integer,
                Variable(10993712),
                Variable(10993713),
                [zero.clone(), zero.clone(), zero.clone(), body],
            )
            .unwrap()
            .into_term()
        };
        let exports = KernelTermExport::integer_export_count();
        let ((root, last_hash), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut root = leaf;
            let mut last_hash = 0;
            for _ in 0..depth {
                root = KernelTerm::integer_operation(
                    KernelIntegerOperator::Multiply,
                    vec![root.clone(), root],
                )
                .unwrap();
                let field = StoredIntegerTerm::from_root(root.clone()).unwrap();
                last_hash = hash(&field);
                assert_eq!(hash(&field), last_hash);
            }
            (root, last_hash)
        });
        let field = StoredIntegerTerm::from_root(root.clone()).unwrap();
        assert_eq!(hash(&field), last_hash);
        let folded = wrap(root.clone());
        let retained = StoredIntegerTerm::from_root(folded.clone()).unwrap();
        let native_id = retained
            .root()
            .unwrap()
            .retained_integer_exact_id()
            .unwrap();
        let retained_hash = hash(&retained);
        assert_ne!(
            retained,
            StoredIntegerTerm::from_root(wrap(distinct)).unwrap()
        );
        assert!(!root.has_cached_native_argument());
        assert!(!folded.has_cached_native_argument());
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        for _ in 0..2 {
            let native = KernelTermExport::default().integer(&folded).unwrap();
            assert_eq!(native.id(), native_id);
            let input = StoredIntegerTerm::from(native.as_ref().clone());
            assert_eq!(retained, input);
            assert_eq!(retained.cmp(&input), std::cmp::Ordering::Equal);
            assert_eq!(retained_hash, hash(&input));
            drop(input);
            let weak = native.downgrade();
            drop(native);
            assert_eq!(weak.upgrade().as_ref(), Some(&folded));
        }
        measured.push(work);
    }
    assert!(
        measured.windows(2).all(|work| work[1] <= 5 * work[0]),
        "{measured:?}"
    );
}

#[test]
fn stored_machine_quantity_reads_the_cached_word_without_export() {
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let mut root = KernelTermImport::default().machine(format, &MachineTerm::constant(1));
    let mut symbolic =
        KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998990));
    for depth in 1..=16 {
        let double = |child: KernelTerm| {
            KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [child.clone(), child])
        };
        root = double(root);
        symbolic = double(symbolic);
        if depth % 4 == 0 {
            for (operand, expected) in [(&root, Some(1 << depth)), (&symbolic, None)] {
                let stored = StoredMachineTerm::from_value(ExecutionValue::Shared(operand.clone()))
                    .expect("stored machine quantity");
                let (constant, work) =
                    crate::instrumentation::measure_deterministic_work(|| stored.as_const());
                assert_eq!(constant, expected);
                assert!(!operand.has_cached_native_argument());
                assert!(work <= 2, "depth={depth}, work={work}");
            }
        }
    }
}
