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
