use super::*;

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
            let mut bits = Bitvector32Term::Variable(Variable(921_000));
            for i in 0..size {
                bits = Bitvector32Term::Binary {
                    format: MachineIntegerType::Int32,
                    op: match i % 3 {
                        0 => MachineBinaryOp::Add,
                        1 => MachineBinaryOp::ShiftLeft,
                        _ => MachineBinaryOp::ShiftRight,
                    },
                    left: Box::new(bits),
                    right: Box::new(Bitvector32Term::Constant(1)),
                };
            }
            let source = PureFunctionArgument::Value(CValue::Int32(bits));
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
            let mut bits = Bitvector32Term::Variable(Variable(931_000));
            for _ in 0..size {
                bits = Bitvector32Term::UInt32From64(Box::new(Bitvector32Term::UInt64From32(
                    Box::new(bits),
                )));
            }
            let source = PureFunctionArgument::Value(CValue::UInt32(bits));
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
            let mut bits = Bitvector32Term::Variable(Variable(941_000));
            for _ in 0..size {
                bits = Bitvector32Term::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: Box::new(bits),
                    right: Box::new(Bitvector32Term::Constant(1)),
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
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::IntegerToMachine {
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
            let source = PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::BoolCast {
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
            let mut term = KernelTerm::variable(KernelType::C(CType::Int64), Variable(952000));
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
            let mut term = KernelTerm::variable(KernelType::C(CType::Int64), Variable(956000));
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
                                    .machine(format, &Bitvector32Term::Int64Constant(2)),
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
