use super::*;

#[test]
fn retained_execution_handoffs_do_not_walk_the_value_dag() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let leaf = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998241));
        let mut root = leaf.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root, leaf.clone()],
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut outcome = ExpressionOutcome::Value(ExecutionValue::from(root.clone()));
            for _ in 0..32 {
                outcome = outcome.map_value(|value| value.clone());
            }
            let ExpressionOutcome::Value(value) = outcome else {
                unreachable!()
            };
            assert_eq!(value.program_type(), ProgramType::UInt32);
            let (_, MachineOperandView::Shared(selected)) = value.machine().unwrap() else {
                panic!("shared operand")
            };
            assert_eq!(selected, &root);
            value
        });
        assert_eq!(value, ExecutionValue::Shared(root));
        assert_eq!(
            work, 0,
            "handoffs must not visit the selected DAG at size {size}"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn retaining_pointer_read_results_ignores_unrelated_read_definitions() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        for n in 0..unrelated {
            memory.symbolic_pointer_load(
                &Pointer::symbolic(Variable(1019000 + n)),
                ProgramType::Int32Pointer,
            );
        }
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let values = (0..size)
                .map(|n| {
                    memory.symbolic_pointer_load(
                        &Pointer::symbolic(Variable(1020000 + n)),
                        ProgramType::Int32Pointer,
                    )
                })
                .collect::<Vec<_>>();
            let exports = KernelTermExport::machine_export_count();
            let (retained, work) = crate::instrumentation::measure_deterministic_work(|| {
                values
                    .into_iter()
                    .map(ExecutionValue::retain_native)
                    .collect::<Vec<_>>()
            });
            assert!(retained.iter().all(|value| matches!(
                value.shared().map(KernelTerm::node),
                Some(KernelTermNode::PointerRead { .. })
            )));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(
                work <= 64 * size as usize,
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
fn pointer_branch_handoffs_retain_selected_dags_without_export() {
    let _session = crate::kernel::VerificationSession::enter();
    let value = SharedPointerValue::import(&PointerValue::new(
        Pointer::symbolic(Variable(1026300)),
        ProgramType::Int32Pointer,
    ));
    for unrelated in [0, 128, 512] {
        let _unrelated = (0..unrelated)
            .map(|i| KernelTerm::variable(KernelType::Integer, Variable(1026301 + i)))
            .collect::<Vec<_>>();
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1026900));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [argument.clone(), argument],
                );
            }
            let root = KernelTerm::shared_pointer_call(
                KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "selected".into(),
                    vec![argument],
                ),
                value.clone(),
            );
            let exports = KernelTermExport::machine_export_count();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut value = ExecutionValue::Shared(root.clone());
                for _ in 0..32 {
                    value = value.retain_pointer_result();
                }
                value
            });
            assert_eq!(result.shared(), Some(&root));
            assert_eq!(work, 0, "size={size} unrelated={unrelated}");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn pointer_local_bindings_preserve_prepared_dags_at_constant_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let payload = SharedPointerValue::import(&PointerValue::new(
        Pointer::symbolic(Variable(1027200)),
        ProgramType::Int32Pointer,
    ));
    for unrelated in [0, 128, 512] {
        let mut state = ExecutionState::new();
        for n in 0..unrelated {
            state.locals.set_typed(
                format!("unrelated_{n}"),
                ProgramValue::Int32(MachineTerm::constant(n)),
                ProgramType::Int32,
            );
        }
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1027201));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [argument.clone(), argument],
                );
            }
            let root = KernelTerm::shared_pointer_call(
                KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "local_source".into(),
                    vec![argument],
                ),
                payload.clone(),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for n in 0..32 {
                    state.locals.set_retained_typed_with_all_qualifiers(
                        "selected",
                        ExecutionValue::Shared(root.clone()),
                        ProgramType::Int32Pointer,
                        false,
                        n % 2 == 0,
                        false,
                        n % 3 == 0,
                    );
                    assert!(matches!(
                        state
                            .locals
                            .get("selected")
                            .unwrap()
                            .shared()
                            .unwrap()
                            .node(),
                        KernelTermNode::PointerCall { .. }
                    ));
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work < 4096, "size={size} unrelated={unrelated} work={work}");
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

#[test]
fn retained_pointer_cells_do_not_export_prepared_dags_or_scan_sibling_cells() {
    for unrelated in [0, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for n in 0..unrelated {
            memory = memory.store(
                Memory::local_pointer(format!("unrelated_pointer_cell_{n}")),
                ProgramValue::Int32(MachineTerm::constant(n)),
            );
        }
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1027700));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [argument.clone(), argument],
                );
            }
            let pointer = PointerValue::new(
                Pointer::symbolic(Variable(1027701 + size)),
                ProgramType::Int32Pointer,
            );
            let root = KernelTerm::shared_pointer_call(
                KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "stored".into(),
                    vec![argument],
                ),
                SharedPointerValue::import(&pointer),
            );
            let address = Memory::local_pointer(format!("selected_{size}"));
            let exports = KernelTermExport::machine_export_count();
            let (stored, work) = crate::instrumentation::measure_deterministic_work(|| {
                let stored = memory
                    .clone()
                    .store_retained(address.clone(), root.clone().into());
                for _ in 0..16 {
                    assert_eq!(
                        stored.known_retained_value(&address).unwrap().shared(),
                        Some(&root)
                    );
                }
                stored
            });
            assert_eq!(
                stored.known_retained_value(&address).unwrap().shared(),
                Some(&root)
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work <= 128, "size={size} unrelated={unrelated} work={work}");
        }
    }
}

#[test]
fn boolean_storage_handoffs_do_not_walk_expression_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf = KernelTerm::variable(KernelType::Bool, Variable(999510));
        let mut root = leaf.clone();
        for index in 0..size {
            root = KernelTerm::boolean_if([
                KernelTerm::variable(KernelType::Bool, Variable(999511 + index as u64)),
                root,
                leaf.clone(),
            ]);
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                let value = ExecutionValue::Shared(root.clone());
                assert!(value.pointer().is_none());
                let stored = StoredExecutionValue::from(value);
                assert_eq!(stored.clone().into_value().shared(), Some(&root));
                let cell = StoredMemoryValue::from(stored.into_value());
                assert_eq!(cell.into_value().shared(), Some(&root));
            }
        });
        assert_eq!(work, 0, "size={size}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn float_local_handoffs_retain_growing_shared_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let mut root = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(1008301),
            );
            for _ in 0..size {
                root = KernelTerm::float_binary(
                    format,
                    FloatBinaryOperator::Add,
                    [root.clone(), root],
                )
                .unwrap();
            }
            let exports = KernelTermExport::float_export_count();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut state = ExecutionState::new();
                state.locals.set_retained_typed_with_all_qualifiers(
                    "x",
                    ExecutionValue::Shared(root.clone()),
                    format.program_type(),
                    false,
                    false,
                    false,
                    false,
                );
                let stored = state.locals.get("x").unwrap().clone();
                assert_eq!(stored.shared(), Some(&root));
                let separate = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
                assert_eq!(stored, stored.clone());
                assert_eq!(stored, separate);
                assert_eq!(stored.cmp(&separate), std::cmp::Ordering::Equal);
                assert_eq!(stored.into_value().shared(), Some(&root));
            });
            assert!(work <= 100, "size={size}, work={work}");
            assert_eq!(KernelTermExport::float_export_count(), exports);
        }
    }
}

#[test]
fn float_memory_carriers_retain_growing_shared_prefixes() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let mut root = KernelTerm::variable(
                KernelType::Program(format.program_type()),
                Variable(1008400),
            );
            for _ in 0..size {
                root = KernelTerm::float_binary(
                    format,
                    FloatBinaryOperator::Add,
                    [root.clone(), root],
                )
                .unwrap();
            }
            let exports = KernelTermExport::float_export_count();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    let cell = StoredMemoryValue::from(ExecutionValue::Shared(root.clone()));
                    assert_eq!(cell.program_type(), format.program_type());
                    assert_eq!(cell.clone().into_value().shared(), Some(&root));
                    assert_eq!(cell.into_value().shared(), Some(&root));
                }
            });
            assert_eq!(work, 0, "size={size}");
            assert_eq!(KernelTermExport::float_export_count(), exports);
        }
    }
}

#[test]
fn machine_storage_keys_hash_growing_shared_operands_without_native_output() {
    use std::hash::{Hash, Hasher};
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let atom = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(998650));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add,
                [root, atom.clone()],
            );
        }
        let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hash);
            hash.finish()
        });
        let (_, repeated) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
                assert_eq!(value.cmp(&value.clone()), std::cmp::Ordering::Equal);
            }
        });
        assert_eq!(
            repeated, 0,
            "warm key operations inspect no operand prefixes"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(value.shared(), Some(&root));
        if let Some(previous) = previous {
            assert!(work <= 5 * previous, "{previous} -> {work}");
        }
        previous = Some(work);
    }
}

#[test]
fn boolean_storage_keys_keep_growing_connectives_shared() {
    use std::hash::{Hash, Hasher};
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let atom = KernelTerm::variable(KernelType::Bool, Variable(998660));
        let other = KernelTerm::variable(KernelType::Bool, Variable(998661));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::boolean_if_raw([atom.clone(), root, other.clone()]);
        }
        assert!(!root.has_cached_native_argument());
        let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hash);
            hash.finish()
        });
        let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..32 {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
            }
        });
        assert_eq!(warm, 0);
        assert!(
            !root.has_cached_native_argument(),
            "key operations must not cache the native Boolean tree"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(previous) = previous {
            assert!(work <= 5 * previous, "{previous} -> {work}");
        }
        previous = Some(work);
    }
}

#[test]
fn float_storage_keys_keep_growing_operands_shared() {
    use std::hash::{Hash, Hasher};
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let atom =
                KernelTerm::variable(KernelType::Program(format.program_type()), Variable(998680));
            let mut root = atom.clone();
            for _ in 0..size {
                root = KernelTerm::float_binary(
                    format,
                    FloatBinaryOperator::Add,
                    [root, atom.clone()],
                )
                .unwrap();
            }
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let exports = KernelTermExport::float_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                stored.hash(&mut hash);
                hash.finish()
            });
            let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    let mut hash = std::collections::hash_map::DefaultHasher::new();
                    stored.hash(&mut hash);
                }
            });
            assert_eq!(warm, 0);
            assert_eq!(KernelTermExport::float_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            if let Some(previous) = previous {
                assert!(work <= 5 * previous, "{previous} -> {work}");
            }
            previous = Some(work);
        }
    }
}
#[test]
fn boolean_storage_key_work_is_independent_of_prior_verifications() {
    use std::hash::Hash;
    for size in [16, 64, 256] {
        let atom = KernelTerm::variable(KernelType::Bool, Variable(998710));
        let other = KernelTerm::variable(KernelType::Bool, Variable(998711));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::boolean_if_raw([atom.clone(), root, other.clone()]);
        }
        let mut cold = Vec::new();
        for _ in 0..2 {
            let _session = crate::kernel::VerificationSession::enter();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
            });
            cold.push(work);
            let _nested = crate::kernel::VerificationSession::enter();
            let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
                let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
            });
            assert_eq!(warm, 0, "nested verification retains its parent's memo");
        }
        assert!(cold[0] > 0);
        assert_eq!(
            cold[0], cold[1],
            "size={size}: session work must not inherit an earlier key cache"
        );
    }
}
#[test]
fn float_storage_key_work_is_independent_of_prior_verifications() {
    use std::hash::Hash;
    for size in [16, 64, 256] {
        let atom =
            KernelTerm::variable(KernelType::Program(ProgramType::Float64), Variable(998715));
        let mut root = atom.clone();
        for _ in 0..size {
            root = KernelTerm::float_binary(
                KernelFloatType::Float64,
                FloatBinaryOperator::Add,
                [root, atom.clone()],
            )
            .unwrap();
        }
        let mut cold = Vec::new();
        for _ in 0..2 {
            let _session = crate::kernel::VerificationSession::enter();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
            });
            cold.push(work);
            let _nested = crate::kernel::VerificationSession::enter();
            let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
                let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                value.hash(&mut hash);
            });
            assert_eq!(warm, 0, "nested verification retains its parent's memo");
        }
        assert!(cold[0] > 0);
        assert_eq!(
            cold[0], cold[1],
            "size={size}: session work must not inherit an earlier key cache"
        );
    }
}
