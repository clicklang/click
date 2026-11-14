use super::*;

#[test]
fn retained_bitwise_masks_scale_without_exporting_prefixes() {
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut execution = ExecutionBudget::new();
        let budget = SpecEvaluation::logical(&mut execution);
        let mut root: SpecValue =
            ProgramValue::UInt64(MachineTerm::Variable(Variable(993470))).into();
        let mask: SpecValue = ProgramValue::UInt64(MachineTerm::uint64_constant(!3)).into();
        let tag: SpecValue = ProgramValue::UInt64(MachineTerm::uint64_constant(1)).into();
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = apply_values(Some(MachineBinaryOp::BitwiseOr), &root, &tag, &budget)
                    .unwrap()
                    .value
                    .into();
                root = apply_values(Some(MachineBinaryOp::BitwiseAnd), &root, &mask, &budget)
                    .unwrap()
                    .value
                    .into();
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(work[1] <= 5 * work[0] && work[2] <= 5 * work[1], "{work:?}");
}

#[test]
fn retained_xor_normalizes_only_its_selected_component_without_exports() {
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(993480)));
        for index in 1..size {
            let next = KernelTermImport::default()
                .machine(format, &MachineTerm::Variable(Variable(993480 + index)));
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::BitwiseXor,
                [root, next],
            );
        }
        let left: SpecValue = root.into();
        let right: SpecValue = ProgramValue::UInt32(MachineTerm::Variable(Variable(993480))).into();
        let mut execution = ExecutionBudget::new();
        let budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::machine_export_count();
        let (result, measured) = crate::instrumentation::measure_deterministic_work(|| {
            apply_values(Some(MachineBinaryOp::BitwiseXor), &left, &right, &budget).unwrap()
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let native = left.into_native();
        let ProgramValue::UInt32(native) = native else {
            panic!("word");
        };
        let expected =
            MachineTerm::bitwise_xor_at(format, native, MachineTerm::Variable(Variable(993480)));
        assert_eq!(
            SpecValue::from(result.value).into_native(),
            ProgramValue::UInt32(expected)
        );
        work.push(measured);
    }
    // The selected xor component is explicit input and its canonical result
    // has one node per surviving operand. No ambient fact index is scanned.
    assert!(work[1] <= 8 * work[0] && work[2] <= 8 * work[1], "{work:?}");
}

#[test]
fn retained_tag_facts_use_constant_work_in_growing_contexts() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let f = MachineIntegerType::UInt64;
        let word = MachineTerm::Variable(Variable(995610));
        let tag = MachineTerm::Variable(Variable(995611));
        let mut context = PureFactContext::new();
        for n in 0..size {
            for variable in [Variable(995612 + n), Variable(995610)] {
                context = context.assume_condition(
                    ConditionTerm::unsigned_less_equal(
                        MachineTerm::Variable(variable),
                        MachineTerm::uint32_constant(1000 + n as u32),
                    ),
                    true,
                );
            }
        }
        context = context
            .assume_condition(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), tag.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(tag.clone(), MachineTerm::constant(1)),
                true,
            );
        let inner = MachineTerm::uint64_bitwise_or(word, MachineTerm::uint64_from_int32(tag));
        let left = input(f, &inner, true);
        let right = input(f, &MachineTerm::uint64_constant(!3), true);
        let result = bitwise::apply(MachineBinaryOp::BitwiseAnd, &left, &right)
            .unwrap()
            .value;
        let exports = KernelTermExport::machine_export_count();
        let (fact, work) = crate::instrumentation::measure_deterministic_work(|| {
            bitwise::tag_equation(&result, &context)
        });
        assert!(fact.is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(samples.iter().all(|w| *w <= samples[0] + 8), "{samples:?}");
}

#[test]
fn retained_bitwise_operations_do_not_export_growing_arithmetic_operands() {
    for f in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut root = KernelTerm::retained_machine_operand(
                f,
                MachineOperandView::Legacy(&MachineTerm::Variable(Variable(995615))),
            );
            let one = KernelTerm::retained_machine_operand(
                f,
                MachineOperandView::Legacy(
                    &crate::kernel::machine_integer::range::constant_word(f, &1.into()).unwrap(),
                ),
            );
            let right = input(f, &MachineTerm::Variable(Variable(995616)), true);
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    root = KernelTerm::machine_binary_shared(
                        f,
                        MachineBinaryOp::Add,
                        [root.clone(), one.clone()],
                    );
                    for op in [
                        MachineBinaryOp::BitwiseAnd,
                        MachineBinaryOp::BitwiseOr,
                        MachineBinaryOp::BitwiseXor,
                    ] {
                        bitwise::apply(op, &root.clone().into(), &right).unwrap();
                    }
                    bitwise_not(&root.clone().into(), None).unwrap();
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            samples.push(work);
        }
        assert!(
            samples[1] <= samples[0] * 5 && samples[2] <= samples[1] * 5,
            "{f:?}: {samples:?}"
        );
    }
}
