use super::*;

#[test]
fn mixed_arithmetic_retains_growing_prefixes_without_exports() {
    for format in FORMATS {
        for op in OPS {
            let mut previous = None;
            for size in [16, 64, 256] {
                let _session = VerificationSession::enter();
                let mut execution = ExecutionBudget::new();
                let budget = SpecEvaluation::logical(&mut execution);
                let mut root = operand(format, &MachineTerm::Variable(Variable(995458)), true);
                let right = operand(
                    MachineIntegerType::UInt16,
                    &MachineTerm::Variable(Variable(995459)),
                    true,
                );
                let exports = KernelTermExport::machine_export_count();
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        root = apply_values(Some(op), &root, &right, &budget)
                            .unwrap()
                            .value
                            .into();
                    }
                });
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(matches!(root, SpecValue::Shared(_)));
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
