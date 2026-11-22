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

#[test]
fn integer_fold_capture_summary_scales_without_integer_exports() {
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Variable(91_000);
        let accumulator = Variable(91_001);
        let item = Variable(91_002);
        let mut body = KernelTerm::variable(KernelType::Integer, source);
        for index in 0..size {
            let term =
                KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![body.clone(), body])
                    .unwrap();
            body = KernelTerm::integer_operation(
                KernelIntegerOperator::Add,
                vec![
                    term,
                    KernelTerm::variable(KernelType::Integer, Variable(92_000 + index)),
                ],
            )
            .unwrap();
        }
        let zero = KernelTerm::integer_literal(0.into());
        let fold = KernelFold::new(
            KernelFoldIndex::Integer,
            accumulator,
            item,
            [zero.clone(), zero.clone(), zero, body],
        )
        .unwrap();

        let samples = [0, 16, 64, 256].map(|unrelated| {
            let replacement = IntegerTerm::Variable(accumulator);
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            for index in 0..unrelated {
                let other = KernelTerm::variable(KernelType::Integer, Variable(95_000 + index));
                assert_eq!(rewrite.body_variable_max(&other), Some(95_000 + index));
            }
            let exports = KernelTermExport::integer_export_count();
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| rewrite.retained_fold(&fold));
            let result = result.unwrap();
            assert!(result.accumulator.0 > 92_000 + size - 1);
            assert_eq!(result.item, item);
            assert_eq!(KernelTermExport::integer_export_count(), exports);
            work
        });
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
        assert!(
            samples[0] <= 160 * size as usize + 400,
            "size={size}, work={samples:?}"
        );
    }
}
