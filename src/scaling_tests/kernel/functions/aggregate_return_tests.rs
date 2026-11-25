// Scaling tests of `src/kernel/functions/aggregate_return_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn construction_destination_binding_work_ignores_unrelated_caller_objects() {
    let mut work_by_size = Vec::new();
    for count in [4, 32, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut caller = allocate_destination(
            &ExecutionState::new().with_population_creation_tracking(),
            "node",
        );
        let at = caller.locals.slot("node").unwrap().clone();
        caller = caller.with_aggregate_return_destination(at, node_layout());
        for index in 0..count {
            let unrelated = SymbolicMemory::frame_local_pointer(10, format!("unrelated{index}"));
            caller.memory = caller.memory.with_block(unrelated.base.clone(), 4);
            caller.resources = caller
                .resources
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    unrelated,
                    0u32.into(),
                    1u32.into(),
                )));
        }
        let function = construction_function("node", node_construction_body());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            construction_return::bind(
                &caller,
                function.contract_interface(),
                &mut ExecutionState::new().with_population_creation_tracking(),
                None,
            )
            .unwrap();
        });
        work_by_size.push(work);
    }
    assert!(
        work_by_size
            .iter()
            .all(|work| *work <= work_by_size[0].max(1) * 2),
        "{work_by_size:?}"
    );
    {
        let costs = work_by_size.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 32);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([4, 32, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
fn construction_completion_work_scales_with_value_fields() {
    for parameter in [false, true] {
        let mut samples = Vec::new();
        for count in [8, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            // Leave padding between fields so initialization retains separate
            // runs instead of measuring only one contiguous initialized range.
            let layout = AggregateLayout::new(
                count * 8,
                8,
                (0..count)
                    .map(|index| {
                        AggregateField::new(format!("field{index}"), index * 8, ProgramType::Int32)
                    })
                    .collect(),
            );
            let at = OldAddress::symbolic(Variable(873_004));
            register_block_alignment(&at.base, 8);
            // Native constructor contracts hold separate field owners; include
            // their growing index, rather than only one whole-object owner.
            let resources = if parameter {
                (0..count).fold(ResourceContext::new(), |resources, index| {
                    resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                        at.offset_by_bytes(index * 8),
                        0u32.into(),
                        1u32.into(),
                    )))
                })
            } else {
                ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
                    MemoryRange::new(at.clone(), 0u32.into(), (count * 2).into()),
                ))
            };
            let caller = ExecutionState::new()
                .with_population_creation_tracking()
                .with_memory(
                    SymbolicMemory::new().with_uninitialized_block(at.base.clone(), count * 8),
                )
                .with_resource_context(resources)
                .with_aggregate_return_destination(at.clone(), layout.clone());
            let function = if parameter {
                program_function(
                    ProgramType::Void,
                    "wide_constructor",
                    vec![program_parameter("destination", ProgramType::Int32Pointer)],
                    program_skip(),
                )
                .with_construction_parameter(0, layout)
            } else {
                program_function(
                    ProgramType::VoidPointer,
                    "wide_result",
                    vec![],
                    program_skip(),
                )
                .with_construction_return(layout)
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut state = caller.clone().with_local(
                    "destination",
                    ProgramValue::typed_pointer(at.clone(), ProgramType::Int32Pointer),
                );
                construction_return::bind(&caller, function.contract_interface(), &mut state, None)
                    .unwrap();
                construction_return::initialize_summary(&mut state, &caller);
                if parameter {
                    assert!(
                        construction_return::complete_parameter(
                            &state,
                            function.contract_interface()
                        )
                        .is_none()
                    );
                } else {
                    construction_return::complete(
                        &state,
                        function.contract_interface(),
                        ProgramValue::typed_pointer(at.clone(), ProgramType::VoidPointer),
                    )
                    .unwrap();
                }
            });
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 6),
            "{samples:?}"
        );
    }
}

// Query work is bounded by potentially aliasing tracked objects, not other
// caller allocations. Concrete unrelated raw objects are excluded by the index.
#[test]
fn construction_initialization_lookup_ignores_unrelated_caller_storage() {
    let mut work_by_size = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = SymbolicMemory::frame_local_pointer(21, "construction");
        let mut memory = SymbolicMemory::new().with_uninitialized_block(source.base.clone(), 4);
        for index in 0..count {
            memory = memory.with_uninitialized_block(format!("local:unrelated:{index}"), 4);
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.may_read_uninitialized_object(&source, 4)
        });
        assert!(result);
        work_by_size.push(work);
    }
    assert!(
        work_by_size
            .iter()
            .all(|work| *work <= work_by_size[0].max(1) * 2),
        "{work_by_size:?}"
    );
}

#[test]
fn aggregate_return_copy_permission_ignores_unrelated_storage() {
    let mut samples = Vec::new();
    for count in [4, 32, 256] {
        let temporary = OldAddress::verifier_temporary(Variable(870_201));
        let mut memory = SymbolicMemory::new().with_block(temporary.base.clone(), 16);
        for index in 0..count {
            memory = memory.with_block(AddressBase::Heap(880_000 + index), 16);
        }
        let state = ExecutionState::new().with_memory(memory);
        let source = OldPointer::new(temporary, ProgramType::UInt8Pointer);
        let layout = node_layout();
        let assumptions = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                crate::kernel::eval::missing_aggregate_copy_read_resource(
                    &state,
                    &source,
                    &layout,
                    &assumptions
                )
                .is_none()
            );
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn materialized_return_storage_ignores_unrelated_local_declarations() {
    let mut samples = Vec::new();
    for count in [4, 32, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = SymbolicMemory::frame_local_pointer(999, "source");
        let mut state = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block(source.base.clone(), 16)
                .store(
                    source.clone(),
                    ProgramValue::typed_pointer(OldAddress::null(), ProgramType::Int32Pointer),
                )
                .store(source.offset_by_bytes(8), int32(37)),
        );
        let owner = LocalFunctionId::new(None, "return_scaling".into());
        for ordinal in 0..count {
            let binding = LocalBindingId::new(
                owner.clone(),
                false,
                ordinal,
                Some(format!("unrelated_{ordinal}")),
            );
            state.locals.set(binding, int32(0));
        }
        let function = copy_function();
        let (returned, work) = crate::instrumentation::measure_deterministic_work(|| {
            complete_aggregate_return(
                &mut state,
                &function,
                ProgramValue::typed_pointer(source.clone(), ProgramType::VoidPointer),
            )
            .unwrap()
        });
        assert_eq!(
            pointer(&returned).base,
            AddressBase::AggregateReturn { frame: 0 }
        );
        assert_eq!(
            state
                .memory
                .known_value(&pointer(&returned).offset_by_bytes(8)),
            Some(int32(37))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
