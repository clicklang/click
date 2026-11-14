use super::*;

#[test]
fn wide_cast_chains_retain_prefixes_with_linear_work() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut value: SpecValue = root(
            MachineIntegerType::Int128,
            &MachineTerm::Variable(Variable(995720)),
        )
        .into();
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                value = cast(&value, ProgramType::UInt32).unwrap().into();
                value = cast(&value, ProgramType::Int128).unwrap().into();
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(work[1] <= 5 * work[0] && work[2] <= 5 * work[1], "{work:?}");
}

#[test]
fn wide_quotient_chains_retain_integer_sources_with_linear_work() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let mut value: SpecValue = root(
            MachineIntegerType::Int128,
            &MachineTerm::Variable(Variable(995721)),
        )
        .into();
        let divisor: SpecValue =
            ProgramValue::Int128(word(MachineIntegerType::Int128, 3.into())).into();
        let mut execution = ExecutionBudget::new();
        let budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                value = apply_values(Some(MachineBinaryOp::Divide), &value, &divisor, &budget)
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
