use super::*;

#[test]
fn retained_contract_result_storage_and_exit_memory_skip_expression_prefixes() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(998340)));
        let three = KernelTermImport::default().machine(format, &MachineTerm::uint32_constant(3));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Multiply,
                [root, three.clone()],
            );
        }
        let value = StoredExecutionValue::from(ExecutionValue::from(root.clone()));
        let function = program_function(
            ProgramType::UInt32,
            "result",
            Vec::new(),
            program_return(crate::kernel::program_expression::uint32_literal(0)),
        );
        let mut state = ExecutionState::new();
        let caller = ExecutionState::new();
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                set_function_result(&mut state, &function, value.clone());
                let memory = function_exit_memory(&caller, &state, &value, &function).unwrap();
                assert_eq!(&memory, state.memory());
            }
        });
        assert_eq!(
            state.locals.get(CONTRACT_RESULT).unwrap().shared(),
            Some(&root)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert_eq!(work, [0, 0, 0], "no expression traversal at these handoffs");
}

#[test]
fn pointer_return_handoffs_retain_prepared_dags_without_export() {
    let _session = crate::kernel::VerificationSession::enter();
    let function = program_function(
        ProgramType::Int32Pointer,
        "result",
        Vec::new(),
        program_return(crate::kernel::program_expression::int32_literal(0)),
    );
    let payload = SharedPointerValue::import(&Pointer::new(
        Address::symbolic(Variable(1027300)),
        ProgramType::Int32Pointer,
    ));
    for unrelated in [0, 128, 512] {
        let mut state = ExecutionState::new();
        for n in 0..unrelated {
            state.locals.set_typed(
                format!("other_{n}"),
                ProgramValue::Int32(MachineTerm::constant(n)),
                ProgramType::Int32,
            );
        }
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let mut argument =
                KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(1027301));
            for _ in 0..size {
                argument = KernelTerm::machine_binary_shared(
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Add,
                    [argument.clone(), argument],
                );
            }
            let root = KernelTerm::shared_pointer_call(
                KernelTerm::checked_call(
                    KernelType::Program(ProgramType::Int32Pointer),
                    "returned".into(),
                    vec![argument],
                ),
                payload.clone(),
            );
            let exports = KernelTermExport::machine_export_count();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..16 {
                    let mut obligations = Vec::new();
                    let value = coerce_retained_function_return_value(
                        ExecutionValue::Shared(root.clone()).into(),
                        &function,
                        &mut obligations,
                        &PureFactContext::new(),
                    )
                    .unwrap();
                    assert_eq!(value.shared(), Some(&root));
                    set_function_result(&mut state, &function, value.clone());
                    assert_eq!(
                        state.locals.get(CONTRACT_RESULT).unwrap().shared(),
                        Some(&root)
                    );
                    crate::kernel::loops::assign_call_result(
                        &mut state,
                        &("received").into(),
                        value,
                        &mut obligations,
                        &PureFactContext::new(),
                    )
                    .unwrap();
                    assert_eq!(state.locals.get("received").unwrap().shared(), Some(&root));
                    assert!(obligations.is_empty());
                }
            });
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(work < 8192, "size={size} unrelated={unrelated} work={work}");
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

#[test]
fn typed_contract_result_lookup_and_update_skip_unrelated_locals() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut locals = LocalEnvironment::new();
        for index in 0..count {
            locals.set(format!("unrelated_{index}"), int32(index));
        }
        locals.set("result", int32(7));
        locals.set(CONTRACT_RESULT, int32(11));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                locals.set(CONTRACT_RESULT, int32(11));
                assert_eq!(
                    locals.get(CONTRACT_RESULT).unwrap().native().as_ref(),
                    &int32(11)
                );
                assert_eq!(locals.get("result").unwrap().native().as_ref(), &int32(7));
            }
        });
        samples.push(work);
    }
    assert_eq!(
        samples, [samples[0]; 3],
        "direct binding operations: {samples:?}"
    );
}

#[test]
fn typed_contract_exception_lookup_and_update_skip_unrelated_locals() {
    let mut samples = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut locals = LocalEnvironment::new();
        for index in 0..count {
            locals.set(format!("unrelated_{index}"), int32(index));
        }
        locals.set("__click_exception", int32(7));
        locals.set(CONTRACT_EXCEPTION, int32(11));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                locals.set(CONTRACT_EXCEPTION, int32(11));
                assert_eq!(
                    locals.get(CONTRACT_EXCEPTION).unwrap().native().as_ref(),
                    &int32(11)
                );
                assert_eq!(
                    locals.get("__click_exception").unwrap().native().as_ref(),
                    &int32(7)
                );
            }
        });
        samples.push(work);
    }
    assert_eq!(
        samples, [samples[0]; 3],
        "direct binding operations: {samples:?}"
    );
}
