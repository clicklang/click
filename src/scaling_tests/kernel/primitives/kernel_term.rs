use super::*;
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn shared_term_bridges_visit_nodes_once_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(900_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 32, 64, 128] {
            let mut source: SharedIntegerTerm = IntegerTerm::Variable(Variable(901_000)).into();
            for _ in 0..size {
                source = IntegerTerm::Add(source.clone(), source).into();
            }
            let ((imported, restored), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let imported = KernelTermImport::default().integer(&source);
                    let restored = KernelTermExport::default().integer(&imported).unwrap();
                    (imported, restored)
                });
            assert_eq!(restored, source);
            assert_eq!(imported.ty(), &KernelType::Integer);
            assert!(
                work <= 12 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_term_bridge_is_linear_in_explicit_tree_size() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(920_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(921_000));
            for i in 0..size {
                bits = MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: match i % 3 {
                        0 => MachineBinaryOp::Add,
                        1 => MachineBinaryOp::ShiftLeft,
                        _ => MachineBinaryOp::ShiftRight,
                    },
                    left: Box::new(bits),
                    right: Box::new(MachineTerm::constant(1)),
                };
            }
            let source = PureFunctionArgument::Value(ProgramValue::Int32(bits));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 8 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn specialized_cast_bridge_is_linear_beside_unrelated_terms() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(930_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(931_000));
            for _ in 0..size {
                bits = MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(MachineTerm::legacy_cast(
                        MachineCastSpelling::UInt64From32,
                        Box::new(bits),
                    )),
                );
            }
            let source = PureFunctionArgument::Value(ProgramValue::UInt32(bits));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            // Two unary casts per level, one leaf; import, intern and export
            // each charge constant work per explicit node.
            assert!(
                work <= 8 * (2 * size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_observation_bridge_scales_with_its_explicit_operand() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(940_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut bits = MachineTerm::Variable(Variable(941_000));
            for _ in 0..size {
                bits = MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(bits),
                    right: Box::new(MachineTerm::constant(1)),
                };
            }
            let machine = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, bits);
            let source: SharedIntegerTerm = IntegerTerm::Machine(machine.clone()).into();
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().integer(&source);
                drop(source);
                KernelTermExport::default().integer(&term).unwrap()
            });
            assert!(
                matches!(restored.as_ref(), IntegerTerm::Machine(actual) if actual.id() == machine.id())
            );
            assert!(
                work <= 8 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn integer_conversion_bridge_scales_with_shared_operand() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(950_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut value: SharedIntegerTerm = IntegerTerm::Variable(Variable(951_000)).into();
            for _ in 0..size {
                value = IntegerTerm::Add(value.clone(), value).into();
            }
            let source =
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::IntegerToMachine {
                    value,
                    destination: MachineIntegerType::Int32,
                }));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 12 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn boolean_conversion_bridge_is_linear_in_explicit_conditions() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(962_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut condition = ConditionTerm::Variable(Variable(963_000));
            for _ in 0..size {
                condition = ConditionTerm::BoolIf {
                    condition: Box::new(ConditionTerm::Variable(Variable(963_001))),
                    then_condition: Box::new(condition),
                    else_condition: Box::new(ConditionTerm::Constant(false)),
                };
            }
            let source = PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::BoolCast {
                to: MachineIntegerType::Int32,
                value: Box::new(condition),
            }));
            let (restored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let term = KernelTermImport::default().argument(&source);
                KernelTermExport::default().argument(&term).unwrap()
            });
            assert_eq!(restored, source);
            assert!(
                work <= 24 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn integer_comparison_bridge_reconstructs_shared_operands_linearly() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(965_000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut value: SharedIntegerTerm = IntegerTerm::Variable(Variable(966_000)).into();
            for _ in 0..size {
                value = IntegerTerm::Add(value.clone(), value).into();
            }
            let source = ConditionTerm::IntegerGreaterEqual(value.clone(), value);
            let ((term, restored), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    let term = KernelTermImport::default().condition(&source);
                    drop(source);
                    let restored = KernelTermExport::condition(&term).unwrap();
                    (term, restored)
                });
            assert_eq!(KernelTermImport::default().condition(&restored), term);
            assert!(
                work <= 24 * (size + 2),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn observing_every_shared_machine_prefix_does_not_materialize_operands() {
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(951000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let format = MachineIntegerType::Int64;
            let mut term =
                KernelTerm::variable(KernelType::C(ProgramType::Int64), Variable(952000));
            let mut retained = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    // The boxed expansion would double at every level. Both
                    // observation construction and its Integer bridge must
                    // retain handles, including after bridge memo reset.
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let source: SharedIntegerTerm =
                        IntegerTerm::Machine(observation.clone()).into();
                    let common = KernelTermImport::default().integer(&source);
                    drop(source);
                    clear_integer_bridge_memo();
                    let restored = KernelTermExport::default().integer(&common).unwrap();
                    let IntegerTerm::Machine(actual) = restored.as_ref() else {
                        panic!("machine observation");
                    };
                    assert_eq!(actual.id(), observation.id());
                    assert!(actual.value_reading().is_none());
                    assert!(!actual.has_boxed_operand());
                    retained.push(restored);
                }
            });
            assert!(
                work <= 20 * size,
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn machine_root_checking_views_keep_shared_prefixes_unboxed() {
    let mut baseline = Vec::new();
    for unrelated in [0, 128, 512] {
        let mut costs = Vec::new();
        let _ambient = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(955000 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let format = MachineIntegerType::Int64;
            let mut term =
                KernelTerm::variable(KernelType::C(ProgramType::Int64), Variable(956000));
            let mut retained = Vec::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    term = KernelTerm::arithmetic_binary(
                        format,
                        MachineBinaryOp::Add,
                        [term.clone(), term.clone()],
                    )
                    .unwrap();
                    let observation =
                        SharedMachineIntegerTerm::from_shared(format, term.clone()).unwrap();
                    let source = IntegerTerm::Machine(observation.clone());
                    let exact =
                        crate::kernel::machine_integer::identity::mathematical(&source).unwrap();
                    assert_eq!(exact.0, format);
                    assert_eq!(
                        crate::kernel::machine_integer::identity::additive_mathematical(&source),
                        Some(exact)
                    );
                    assert!(
                        crate::kernel::machine_integer::bounds::operation_bound(&observation, true)
                            .is_none()
                    );
                    let range =
                        crate::kernel::machine_integer::range::range_fact(&observation, true);
                    assert!(
                        crate::kernel::proof::integer_arithmetic::integer_affine_claim(&range)
                            .is_some()
                    );
                    let quotient = KernelTerm::intern(
                        KernelType::C(format.c_type()),
                        KernelTermNode::MachineBinary {
                            format,
                            operator: MachineBinaryOp::Divide,
                            arguments: [
                                term.clone(),
                                KernelTermImport::default()
                                    .machine(format, &MachineTerm::int64_constant(2)),
                            ],
                        },
                    );
                    let quotient = SharedMachineIntegerTerm::from_shared(format, quotient).unwrap();
                    for upper in [false, true] {
                        assert!(
                            crate::kernel::machine_integer::bounds::operation_bound(
                                &quotient, upper
                            )
                            .is_some()
                        );
                    }
                    assert!(!quotient.has_boxed_operand());
                    assert!(!observation.has_boxed_operand());
                    retained.push(source);
                }
            });
            costs.push((size, work));
        }
        for pair in costs.windows(2) {
            let [(small, small_work), (large, large_work)] = pair else {
                unreachable!()
            };
            assert!(
                large_work * small * 4 <= small_work * large * 5,
                "{costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "unrelated terms must not add checking work"
            );
        }
    }
}

#[test]
fn retained_load_terms_grow_without_rewalking_snapshots_or_prior_arithmetic() {
    for unrelated in [0, 128, 512] {
        let mut memory = Memory::new();
        for index in 0..unrelated {
            memory = memory.with_block(format!("unrelated-read-{index}"), 4);
        }
        let memory = intern_c_memory(memory);
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut root =
                KernelTerm::variable(KernelType::C(ProgramType::Int32), Variable(993200));
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for index in 0..size {
                    let read = MachineTerm::MemoryLoad(
                        memory.clone(),
                        Box::new(Pointer::symbolic(Variable(993201 + index))),
                        LoadKind::Int32,
                    );
                    let leaf =
                        KernelTermImport::default().machine(MachineIntegerType::Int32, &read);
                    assert!(matches!(leaf.node(), KernelTermNode::MemoryLoad { .. }));
                    root = KernelTerm::arithmetic_binary(
                        MachineIntegerType::Int32,
                        MachineBinaryOp::Add,
                        [root.clone(), leaf],
                    )
                    .unwrap();
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work <= 8 * size as usize,
                "size={size} unrelated={unrelated} work={work}"
            );
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 5, "{samples:?}");
        }
    }
}

#[test]
fn retained_named_reads_do_not_rewalk_their_address_on_each_import() {
    let _session = crate::kernel::VerificationSession::enter();
    for size in [16, 64, 256] {
        let mut offset = PointerOffsetTerm::Variable(Variable(993500));
        for index in 0..size {
            offset = PointerOffsetTerm::Add(
                Box::new(offset),
                Box::new(PointerOffsetTerm::Variable(Variable(993501 + index))),
            );
        }
        let raw = MachineTerm::MemoryLoad(
            intern_c_memory(Memory::new()),
            Box::new(Pointer {
                block: PointerBlock::Symbolic(Variable(993499)),
                offset,
            }),
            LoadKind::Int32,
        );
        let (name, _) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let expected =
            crate::kernel::eval::registered_scalar_read_term(&name, MachineIntegerType::Int32)
                .unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                assert_eq!(
                    crate::kernel::eval::registered_scalar_read_term(
                        &name,
                        MachineIntegerType::Int32
                    )
                    .unwrap(),
                    expected,
                );
            }
        });
        assert!(work <= 3 * size as usize, "size={size} work={work}");
    }
}

#[test]
fn shared_read_selection_reuses_growing_arithmetic_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let raw = MachineTerm::MemoryLoad(
            intern_c_memory(Memory::new()),
            Box::new(Pointer::symbolic(Variable(994110))),
            LoadKind::Int32,
        );
        let leaf = KernelTermImport::default().machine(MachineIntegerType::Int32, &raw);
        let mut root = leaf.clone();
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::arithmetic_binary(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                )
                .unwrap();
                let reads = crate::kernel::shared_machine_read_leaves(&root, || {
                    crate::instrumentation::record_deterministic_work(1);
                    true
                })
                .unwrap();
                assert_eq!(reads.len(), 1);
                assert_eq!(reads.get(&leaf.id()), Some(&leaf));
                let uses = crate::kernel::shared_machine_read_uses(&root, Some(4), || {
                    crate::instrumentation::record_deterministic_work(1);
                    true
                })
                .unwrap();
                assert_eq!(uses.len(), 1);
                assert_eq!(uses.get(&(leaf.id(), Some(4))), Some(&leaf));
            }
        });
        assert!(work <= 16 * size + 8, "size={size} work={work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn nested_read_address_import_is_linear_beside_unrelated_memory() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for index in 0..unrelated {
            memory = memory.store(
                Pointer::symbolic(Variable(997000 + index)),
                ProgramValue::Int32(MachineTerm::constant(index as u32)),
            );
        }
        let memory = intern_c_memory(memory);
        for depth in [16, 64, 256] {
            let mut raw = MachineTerm::constant(0);
            for _ in 0..depth {
                raw = MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: PointerBlock::Symbolic(Variable(996999)),
                        offset: PointerOffsetTerm::scaled_int32_node(raw, 4),
                    }),
                    LoadKind::Int32,
                );
            }
            let (term, work) = crate::instrumentation::measure_deterministic_work(|| {
                KernelTermImport::default().machine(MachineIntegerType::Int32, &raw)
            });
            assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
            assert_eq!(KernelTermExport::machine(&term).unwrap(), raw);
            assert!(
                work <= 5 * depth + 5,
                "depth={depth}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

#[test]
fn conditional_observation_retyping_matches_native_import_without_expanding_dags() {
    let _session = crate::kernel::VerificationSession::enter();
    let unsigned = MachineIntegerType::UInt32;
    let signed = MachineIntegerType::Int32;
    let a = MachineTerm::Variable(Variable(995910));
    let b = MachineTerm::Variable(Variable(995911));
    let guard = ConditionTerm::unsigned_less_equal(a.clone(), b.clone());
    let native = MachineTerm::If {
        condition: Box::new(guard.clone()),
        then_term: Box::new(a.clone()),
        else_term: Box::new(b),
    };
    let mut import = KernelTermImport::default();
    let original = import.machine_arithmetic(unsigned, &native).unwrap();
    let expected = import.machine_arithmetic(signed, &native).unwrap();
    assert_eq!(original.with_machine_observation_type(signed), expected);
    assert_eq!(expected.with_machine_observation_type(unsigned), original);
    let guard = import.condition(&guard);
    for size in [16, 64, 256] {
        let mut root = original.clone();
        for _ in 0..size {
            root = KernelTerm::machine_if_shared(unsigned, [guard.clone(), root.clone(), root]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (signed_root, work) = crate::instrumentation::measure_deterministic_work(|| {
            root.with_machine_observation_type(signed)
        });
        assert!(work <= 3 * (size + 1), "size={size}, work={work}");
        let (_, repeated) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(root.with_machine_observation_type(signed), signed_root);
        });
        assert_eq!(repeated, 0);
        assert_eq!(signed_root.with_machine_observation_type(unsigned), root);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
