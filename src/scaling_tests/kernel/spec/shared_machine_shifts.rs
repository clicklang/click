use super::*;

#[test]
fn c_shifts_retain_growing_values_and_count_prefixes_without_exports() {
    for a in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        for b in [MachineIntegerType::UInt32, MachineIntegerType::Int64] {
            for op in OPS {
                let mut previous = None;
                for size in [16, 64, 256] {
                    let _session = VerificationSession::enter();
                    let mut execution = ExecutionBudget::new();
                    let budget = SpecEvaluation::logical(&mut execution);
                    let SpecValue::Shared(mut left) =
                        input(a, &MachineTerm::Variable(Variable(995476)), true)
                    else {
                        panic!()
                    };
                    let SpecValue::Shared(mut count) =
                        input(b, &MachineTerm::Variable(Variable(995477)), true)
                    else {
                        panic!()
                    };
                    let one = KernelTermImport::default().machine(
                        b,
                        &crate::kernel::machine_integer::range::constant_word(b, &1.into())
                            .unwrap(),
                    );
                    let exports = KernelTermExport::machine_export_count();
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        for _ in 0..size {
                            count = KernelTerm::machine_binary_shared(
                                b,
                                MachineBinaryOp::Add,
                                [count.clone(), one.clone()],
                            );
                            left = apply_values(
                                Some(op),
                                &left.into(),
                                &count.clone().into(),
                                &budget,
                            )
                            .unwrap()
                            .value;
                        }
                    });
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    if let Some(before) = previous {
                        assert!(
                            work <= before * 5 + 8,
                            "{a:?}/{b:?} {op:?}: {size}: {work} vs {before}"
                        );
                    }
                    previous = Some(work);
                }
            }
        }
    }
}

#[test]
fn retained_int64_order_uses_root_width_bounds_without_walking_prefixes() {
    let mut previous = None;
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let mut root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(995478)));
        let one = KernelTermImport::default().machine(format, &MachineTerm::int64_constant(1));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root, one.clone()],
            );
        }
        let maximum = MachineTerm::int64_constant(i64::MAX);
        let exports = KernelTermExport::machine_export_count();
        let (condition, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                CompareRelation::LessEqual,
                [
                    MachineOperandView::Shared(&root),
                    MachineOperandView::Legacy(&maximum),
                ],
            )
        });
        assert_eq!(condition, ConditionTerm::Constant(true));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if let Some(before) = previous {
            assert!(work <= before + 8, "{size}: {work} vs {before}");
        }
        previous = Some(work);
    }
}

#[test]
fn rust_shift_chains_keep_original_formats_without_exports() {
    for format in FORMATS {
        for op in OPS {
            let mut previous = None;
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let mut root = input(format, &MachineTerm::Variable(Variable(995493)), true);
                let count = input(
                    MachineIntegerType::UInt64,
                    &MachineTerm::Variable(Variable(995494)),
                    true,
                );
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        root = shifts::rust(op, &root, &count).unwrap().value.into();
                    }
                });
                assert_eq!(root.c_type(), format.c_type());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                if let Some(before) = previous {
                    assert!(
                        work <= before * 5 + 8,
                        "{format:?} {op:?}: {size}: {work} vs {before}"
                    );
                }
                previous = Some(work);
            }
        }
    }
}
