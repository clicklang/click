use super::*;

#[test]
fn retained_contract_result_storage_and_exit_memory_skip_expression_prefixes() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let mut root = KernelTermImport::default()
            .machine(format, &OldMachineTerm::Variable(Variable(998340)));
        let three =
            KernelTermImport::default().machine(format, &OldMachineTerm::uint32_constant(3));
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
    // The one charged unit is admitting the contract-result block, once per
    // state, whatever the result's size and however often it is stored.
    assert_eq!(work, [1, 1, 1], "no expression traversal at these handoffs");
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
    let payload = Pointer::new(
        Address::symbolic(Variable(1027300)),
        ProgramType::Int32Pointer,
    )
    .into_shared();
    for unrelated in [0, 128, 512] {
        let mut state = ExecutionState::new();
        for n in 0..unrelated {
            state.locals.set_typed(
                format!("other_{n}"),
                ProgramValue::Int32(OldMachineTerm::constant(n)),
                ProgramType::Int32,
            );
        }
        // The result and destination cells admit their blocks once per state.
        let warm = StoredExecutionValue::from(ExecutionValue::Shared(
            KernelTerm::shared_pointer_value(payload.clone()),
        ));
        set_function_result(&mut state, &function, warm.clone());
        crate::kernel::loops::assign_call_result(
            &mut state,
            &("received").into(),
            warm,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
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

#[test]
fn prepared_argument_checks_lookup_only_the_live_destination_and_its_resources() {
    let mut samples = Vec::new();
    for count in [16, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = LocalFunctionId::new(None, "prepared".into());
        let name = BindingName::from(LocalBindingId::prepared_argument(function.clone(), 0));
        let address = SymbolicMemory::local_lifetime_pointer(1, &name);
        let layout = AggregateLayout::new(4, 4, Vec::new());
        let memory = SymbolicMemory::new().with_block(address.base.clone(), 4);
        let mut state = ExecutionState::new();
        state.set_memory(memory);
        state
            .locals
            .set_aggregate_object_at(name.clone(), layout.clone(), address.clone());
        let token = |key: Address, index: u32| {
            ResourceFact::own_token(
                "logical_state".into(),
                vec![
                    ProgramValue::typed_pointer(key, ProgramType::UInt8Pointer),
                    int32(index),
                ],
            )
        };
        let mut resources = ResourceContext::new();
        for index in 0..count {
            let other = BindingName::from(LocalBindingId::prepared_argument(
                function.clone(),
                index + 1,
            ));
            let other_address = SymbolicMemory::local_lifetime_pointer(1, &other);
            state
                .locals
                .set_aggregate_object_at(other, layout.clone(), other_address.clone());
            resources = resources.unchecked_with_fact(token(other_address, 0));
        }
        let hit = (0..count).fold(resources.clone(), |resources, index| {
            resources.unchecked_with_fact(token(address.clone(), index))
        });
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(is_prepared_aggregate_argument(&state, &address, &layout));
            assert!(!is_prepared_aggregate_argument(
                &state,
                &address.offset_by_bytes(1),
                &layout,
            ));
            assert!(
                resources
                    .prepared_argument_resource_name(&address.base)
                    .is_none()
            );
            assert!(hit.prepared_argument_resource_name(&address.base).is_some());
        });
        samples.push(work);
    }
    assert_eq!(samples, [samples[0]; 3]);
}

#[test]
fn proof_input_rebinding_retains_storage_without_reusing_it_for_calls() {
    let layout = AggregateLayout::new(4, 4, Vec::new());
    let parameter = ProgramParameter::new("parameter", ProgramType::UInt8Pointer)
        .with_aggregate_layout(layout.clone());
    let function = program_function(
        ProgramType::UInt8Pointer,
        "by_value",
        vec![parameter.clone()],
        crate::kernel::program_skip(),
    );
    let other_function = program_function(
        ProgramType::UInt8Pointer,
        "other",
        vec![parameter],
        crate::kernel::program_skip(),
    );
    let schema = ResourceFieldSchema::new(vec![(
        "count".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let model = |id: u64, address: Address| {
        ResourceFact::own(Resource::Instance(
            ResourceInstance::new(
                InstanceId::from_variable(Variable(id)),
                "model".into(),
                vec![ProgramValue::typed_pointer(address, ProgramType::UInt8Pointer).into()].into(),
                schema.clone(),
                vec![int32(0u32).into()].into(),
            )
            .unwrap(),
        ))
    };
    let mut samples = Vec::new();
    for count in [16u32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let placeholder =
            ProgramValue::typed_pointer(Address::symbolic(Variable(1)), ProgramType::UInt8Pointer);
        let mut caller = bind_program_function_arguments_with(
            &ExecutionState::new(),
            &function,
            &[placeholder],
            true,
        )
        .unwrap();
        let address = caller.locals.slot("parameter").unwrap().clone();
        for index in 0..count {
            caller.locals.set(format!("other_{index}"), int32(index));
            let other = model(u64::from(index) + 1, address.offset_by_bytes(index + 1));
            caller.resources = caller.resources.clone().unchecked_with_fact(other);
        }
        let argument = ProgramValue::typed_pointer(address.clone(), ProgramType::UInt8Pointer);
        let values = std::slice::from_ref(&argument);
        let unkeyed =
            crate::kernel::with_resource_keyed_aggregate_proof_inputs(caller.clone(), &function);
        let unkeyed = bind_program_function_arguments(&unkeyed, &function, values).unwrap();
        assert_ne!(unkeyed.locals.slot("parameter"), Some(&address));

        caller.resources = caller
            .resources
            .clone()
            .unchecked_with_fact(model(0, address.clone()));
        let ((caller, entry), work) = crate::instrumentation::measure_deterministic_work(|| {
            let caller =
                crate::kernel::with_resource_keyed_aggregate_proof_inputs(caller, &function);
            let entry = bind_program_function_arguments(&caller, &function, values).unwrap();
            (caller, entry)
        });
        assert_eq!(entry.locals.slot("parameter"), Some(&address));
        assert_eq!(
            entry
                .resources
                .exact_count(&private_aggregate_storage_owner(address.clone(), &layout)),
            1
        );

        // An ordinary call never reuses the proof input: it receives only an
        // object its frontend prepared, so this one is refused.
        assert!(
            bind_program_function_arguments_retained(
                &caller,
                &function,
                values,
                &[],
                &mut Vec::new(),
            )
            .is_none()
        );
        let other_entry =
            bind_program_function_arguments(&caller, &other_function, values).unwrap();
        assert_ne!(other_entry.locals.slot("parameter"), Some(&address));

        let exit = function_exit_memory(&caller, &entry, &argument.into(), &function).unwrap();
        assert!(!exit.has_block(&address.base));
        samples.push(work);
    }
    assert_eq!(samples, [samples[0]; 3]);
}
