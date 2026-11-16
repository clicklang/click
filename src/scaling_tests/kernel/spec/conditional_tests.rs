use super::*;
#[test]
fn growing_conditional_joins_and_observations_keep_shared_prefixes() {
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let mut value = variable(format, 998140);
        let zero = word(format, 0);
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                value = join(
                    &ConditionTerm::Variable(Variable(998150 + index as u64)),
                    &value,
                    &zero,
                );
                assert!(value.observe().is_some());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < size * 100, "size={size}, work={work}");
    }
}

#[test]
fn selected_conditional_checks_retain_arms_at_every_machine_format() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let samples = [16usize, 64, 256].map(|size| {
            let _session = VerificationSession::enter();
            let guard = ConditionTerm::Variable(Variable(998190));
            let facts = PureFactContext::new().assume_condition(guard.clone(), true);
            let mut value = word(format, 1);
            let zero = word(format, 0);
            for _ in 0..size {
                value = join(&guard, &value, &zero);
            }
            let condition = ConditionTerm::integer_equal(
                value.observe().unwrap(),
                IntegerTerm::constant(1.into()),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(facts.decide(&condition), Some(true));
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            (size, work)
        });
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small <= sw * large * 2, "{format:?}: {samples:?}");
        }
    }
}

#[test]
fn identical_conditional_arms_normalize_without_revisiting_shared_suffixes() {
    let samples = [16usize, 64, 256].map(|size| {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let guard =
            KernelTermImport::default().condition(&ConditionTerm::Variable(Variable(998202)));
        let base = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998203));
        let mut root = base.clone();
        for _ in 0..size {
            root = KernelTerm::machine_if_shared(format, [guard.clone(), root.clone(), root]);
        }
        let condition = ConditionTerm::integer_equal(
            SpecValue::Shared(root).observe().unwrap(),
            SpecValue::Shared(base).observe().unwrap(),
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(PureFactContext::new().decide(&condition), Some(true));
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        (size, work)
    });
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small <= sw * large * 2, "{samples:?}");
    }
}

#[test]
fn closed_order_conditionals_ignore_unrelated_facts() {
    let mut baseline = None;
    for size in [0, 16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(ConditionTerm::Variable(Variable(999720 + index)), true);
        }
        let expression = closed_order_if(
            SpecExpression::Value(ProgramValue::UInt64(MachineTerm::Variable(Variable(
                999710,
            )))),
            SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(3))),
            false,
        );
        let exports = KernelTermExport::machine_export_count();
        let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
            lower_closed_order_if(&expression, &facts)
        });
        let expected = lower_closed_order_if(&expression, &PureFactContext::new());
        assert_eq!(path.value, expected.value);
        let first = *baseline.get_or_insert(work);
        assert!(
            work <= first + 64,
            "{size} unrelated facts: {work}, baseline={first}"
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn nested_closed_order_conditionals_lower_with_linear_work() {
    for truth in [true, false] {
        let mut samples = Vec::new();
        for size in [8, 32, 128, 512] {
            let _session = VerificationSession::enter();
            // Grow explicit source while keeping nesting logarithmic.
            let mut layer = (1..=size)
                .map(|n| {
                    SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(
                        n as u64,
                    )))
                })
                .collect::<Vec<_>>();
            while layer.len() > 1 {
                layer = layer
                    .chunks_exact(2)
                    .map(|pair| closed_order_if(pair[0].clone(), pair[1].clone(), truth))
                    .collect();
            }
            let expression = layer.pop().unwrap();
            let exports = KernelTermExport::machine_export_count();
            let (path, work) = crate::instrumentation::measure_deterministic_work(|| {
                lower_closed_order_if(&expression, &PureFactContext::new())
            });
            assert!(
                matches!(path.value, SpecValue::Shared(ref root) if matches!(root.node(), KernelTermNode::MachineIf { .. }))
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work < size * 512, "{size} conditionals: {work}");
            samples.push((size, work));
        }
        for pair in samples.windows(2) {
            let [(small, sw), (large, lw)] = pair else {
                unreachable!()
            };
            assert!(lw * small <= sw * large * 2, "{truth}: {samples:?}");
        }
    }
}
