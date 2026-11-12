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
        let base = KernelTerm::variable(KernelType::C(CType::Int32), Variable(998203));
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
