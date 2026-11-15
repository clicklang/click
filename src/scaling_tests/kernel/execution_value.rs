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
                Memory::local_pointer(&format!("unrelated_pointer_cell_{n}")),
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
            let address = Memory::local_pointer(&format!("selected_{size}"));
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
