use super::*;
#[test]
fn common_call_numeric_consumers_keep_growing_arguments_shared() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut value = call(format, "initial_call");
        let mut execution = ExecutionBudget::new();
        let budget = SpecEvaluation::logical(&mut execution);
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                let observed =
                    SharedMachineIntegerTerm::from_shared(format, value.clone()).unwrap();
                let application = SharedPureApplication::intern(
                    "nested_call".into(),
                    vec![PureFunctionArgument::SharedMachine(observed)],
                );
                let call = KernelTermImport::default().machine_call(format, &application);
                let widened = cast(&call.clone().into(), CType::Int64).unwrap();
                assert!(
                    MachineOperandView::Shared(&widened)
                        .observe(MachineIntegerType::Int64)
                        .is_some()
                );
                value = apply_values(
                    Some(MachineBinaryOp::Add),
                    &call.clone().into(),
                    &call.into(),
                    &budget,
                )
                .unwrap()
                .value;
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn common_call_borrowing_scales_with_arity_and_reuses_the_reading() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let application = SharedPureApplication::intern(
            "many_args".into(),
            (0..size)
                .map(|n| PureFunctionArgument::Integer(IntegerTerm::constant_i64(n).into()))
                .collect(),
        );
        let root =
            KernelTermImport::default().machine_call(MachineIntegerType::Int32, &application);
        let exports = KernelTermExport::machine_export_count();
        let (first, cold) = crate::instrumentation::measure_deterministic_work(|| {
            root.machine_conversion_leaf().unwrap()
        });
        let (second, warm) = crate::instrumentation::measure_deterministic_work(|| {
            root.machine_conversion_leaf().unwrap()
        });
        assert!(std::ptr::eq(first, second));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(warm, 0);
        work.push(cold);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}
