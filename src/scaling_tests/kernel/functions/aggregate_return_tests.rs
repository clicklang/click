// Scaling tests of `src/kernel/functions/aggregate_return_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn construction_destination_binding_work_ignores_unrelated_caller_objects() {
    let mut work_by_size = Vec::new();
    for count in [4, 32, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut caller =
            allocate_destination(&CState::new().with_population_creation_tracking(), "node");
        let at = caller.locals.slot("node").unwrap().clone();
        caller = caller.with_aggregate_return_destination(at, node_layout());
        for index in 0..count {
            let unrelated = CMemory::frame_local_pointer(10, &format!("unrelated{index}"));
            caller.memory = caller.memory.with_block(unrelated.block.clone(), 4);
            caller.resources = caller
                .resources
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
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
                &mut CState::new().with_population_creation_tracking(),
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
            let layout = CAggregateLayout::new(
                count * 8,
                8,
                (0..count)
                    .map(|index| {
                        CAggregateField::new(format!("field{index}"), index * 8, CType::Int32)
                    })
                    .collect(),
            );
            let at = Pointer::symbolic(Variable(873_004));
            register_block_alignment(&at.block, 8);
            // Native constructor contracts hold separate field owners; include
            // their growing index, rather than only one whole-object owner.
            let resources = if parameter {
                (0..count).fold(ResourceContext::new(), |resources, index| {
                    resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                        at.offset_by_bytes(index * 8),
                        0u32.into(),
                        1u32.into(),
                    )))
                })
            } else {
                ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new(at.clone(), 0u32.into(), (count * 2).into()),
                ))
            };
            let caller = CState::new()
                .with_population_creation_tracking()
                .with_memory(CMemory::new().with_uninitialized_block(at.block.clone(), count * 8))
                .with_resource_context(resources)
                .with_aggregate_return_destination(at.clone(), layout.clone());
            let function = if parameter {
                c_function(
                    CType::Void,
                    "wide_constructor",
                    vec![c_parameter("destination", CType::Int32Pointer)],
                    c_skip(),
                )
                .with_construction_parameter(0, layout)
            } else {
                c_function(CType::VoidPointer, "wide_result", vec![], c_skip())
                    .with_construction_return(layout)
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut state = caller.clone().with_local(
                    "destination",
                    CValue::typed_pointer(at.clone(), CType::Int32Pointer),
                );
                construction_return::bind(&caller, function.contract_interface(), &mut state)
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
                        CValue::typed_pointer(at.clone(), CType::VoidPointer),
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
        let source = CMemory::frame_local_pointer(21, "construction");
        let mut memory = CMemory::new().with_uninitialized_block(source.block.clone(), 4);
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
