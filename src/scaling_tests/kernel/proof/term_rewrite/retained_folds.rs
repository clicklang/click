use super::*;

#[test]
fn common_fold_rewrite_scales_with_shared_children_without_machine_exports() {
    for integer in [false, true] {
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let format = MachineIntegerType::Int32;
            let mut body = if integer {
                KernelTerm::variable(KernelType::Integer, Variable(70))
            } else {
                KernelTerm::retained_machine_operand(
                    format,
                    MachineOperandView::Legacy(&MachineTerm::Variable(Variable(70))),
                )
            };
            for _ in 0..size {
                body = if integer {
                    KernelTerm::integer_operation(
                        KernelIntegerOperator::Add,
                        vec![body.clone(), body],
                    )
                    .unwrap()
                } else {
                    KernelTerm::machine_binary_shared(
                        format,
                        MachineBinaryOp::Add,
                        [body.clone(), body],
                    )
                };
            }
            let zero = if integer {
                KernelTerm::integer_literal(0.into())
            } else {
                KernelTerm::retained_machine_operand(
                    format,
                    MachineOperandView::Legacy(&MachineTerm::constant(0)),
                )
            };
            let fold = KernelFold::new(
                if integer {
                    KernelFoldIndex::Integer
                } else {
                    KernelFoldIndex::Int32
                },
                Variable(71),
                Variable(72),
                [zero.clone(), zero, body.clone(), body],
            )
            .unwrap();
            let from = MachineTerm::Variable(Variable(90));
            let to = MachineTerm::Variable(Variable(91));
            let mut rewrite = TermRewrite::for_bits(&from, &to);
            let exports = KernelTermExport::machine_export_count();
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            assert_eq!(result.unwrap(), fold);
            assert!(
                work <= 100 * size + 200,
                "integer={integer} size={size} work={work}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let (result, repeat_work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            assert_eq!(result.unwrap(), fold);
            assert!(
                repeat_work <= 30,
                "integer={integer} size={size} repeat={repeat_work}"
            );
        }
    }
}
