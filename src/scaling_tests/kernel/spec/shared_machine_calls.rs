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

#[test]
fn actual_nested_call_production_and_native_handoffs_scale_linearly() {
    let mut samples = Vec::new();
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let state = CState::new();
        let mut values = crate::persistent::PersistentMap::default();
        let mut root = KernelTerm::variable(KernelType::C(CType::UInt32), Variable(995831));
        let expression = call_expression(
            MachineIntegerType::UInt32,
            vec![SpecExpression::CExpression(CExpression::Variable(
                "x".into(),
            ))],
        );
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                values.insert("x".into(), root.clone());
                let scope = SpecScope {
                    values: Some(&values),
                    ..SpecScope::unbound(&state, None)
                };
                let mut execution = ExecutionBudget::new();
                let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    scope,
                    &expression,
                    &PureFactContext::new(),
                    &mut SpecEvaluation::logical(&mut execution),
                )
                .unwrap();
                assert_eq!(paths.len(), 1);
                let value = paths.pop().unwrap().value;
                let SpecValue::Shared(next) = &value else {
                    panic!("common call result")
                };
                assert_eq!(next.children(), &[root.clone()]);
                let next = next.clone();
                let CValue::UInt32(MachineTerm::ClickFunctionApplication { arguments, .. }) =
                    value.into_native()
                else {
                    panic!()
                };
                let [PureFunctionArgument::SharedMachine(argument)] = arguments.as_slice() else {
                    panic!("retained argument")
                };
                assert_eq!(argument.shared_operand(), Some(&root));
                root = next;
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples[1] <= 5 * samples[0] && samples[2] <= 5 * samples[1],
        "{samples:?}"
    );
}
