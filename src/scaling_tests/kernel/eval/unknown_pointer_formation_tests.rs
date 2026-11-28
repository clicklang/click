use super::*;

#[test]
fn split_formation_selects_the_owned_piece_beside_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let (p, position, facts, mut resources, _) = split_formation_fixture();
        for i in 0..size {
            let other = Pointer::new(
                Address::new(
                    AddressBase::ExternalArgument,
                    AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(932_000 + i)), 4),
                ),
                ProgramType::Int32Pointer,
            );
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::from_pointer_value(&other, 0u32.into(), 3u32.into(), 4),
            ));
        }
        resources.synchronize_memory_equalities(&facts);
        let (allowed, work) = crate::instrumentation::measure_deterministic_work(|| {
            permits_at(&p, &position, &facts, &resources)
        });
        assert!(allowed);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "split formation searched unrelated owners: {samples:?}"
    );
}

#[test]
fn pointer_formation_uses_selected_bounds_beside_unrelated_ranges_and_facts() {
    let mut samples = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let p = pointer(931_000);
        let mut resources = ResourceContext::new().unchecked_with_fact(view(&p, 0, 3));
        let mut facts = PureFactContext::new();
        for i in 0..size {
            let other = pointer(932_000 + i);
            resources = resources.unchecked_with_fact(view(&other, 0, 3));
            facts = facts.assume_proposition(
                other
                    .opaque_coverage_fact(&MemoryRange::from_pointer_value(
                        &other,
                        0u32.into(),
                        3u32.into(),
                        4,
                    ))
                    .unwrap(),
            );
        }
        resources.synchronize_memory_equalities(&facts);
        let (allowed, work) = crate::instrumentation::measure_deterministic_work(|| {
            permits(&p, 12, &facts, &resources)
        });
        assert!(allowed);
        assert!(!permits(&p, 16, &facts, &resources));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "formation searched unrelated bounds: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn symbolic_offset_zero_query_does_not_build_unrelated_stated_keys() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_condition(
                OldConditionTerm::signed_less_than(
                    OldMachineTerm::Variable(Variable(934_000)),
                    OldMachineTerm::constant(10_000 + index as u32),
                ),
                true,
            );
        }
        let before = crate::persistent::persistent_node_allocations();
        let result = pointer_offset_by_elements_paths(
            &ExecutionState::new(),
            Pointer::new(Address::null(), ProgramType::Int32Pointer),
            OldMachineTerm::Variable(Variable(934_001)),
            4,
            false,
            false,
            ExecutionFacts::new(),
            Vec::new(),
            &facts,
        );
        let allocated = crate::persistent::persistent_node_allocations() - before;
        assert!(matches!(
            result.as_slice(),
            [ExpressionPath {
                outcome: ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::PointerArithmetic),
                ..
            }]
        ));
        samples.push((size.ilog2() as usize + 1, allocated));
    }
    let (base_height, base_allocated) = samples[0];
    for (height, allocated) in samples {
        assert!(
            allocated <= base_allocated * height / base_height,
            "zero-offset query allocated {allocated} nodes (baseline {base_allocated})"
        );
    }
}

/// A slice parameter's entry facts, its span and its coverage, are read off
/// its own wide argument (`design/rust-slice-values.md`, step 3b): the
/// entry's work grows linearly with the slice parameters, and the first
/// slice's formation bounds stay one selected fact beside them.
#[test]
fn slice_entry_facts_grow_linearly_with_slice_parameters() {
    let sizes = [8u64, 32, 128];
    let mut samples = Vec::new();
    for size in sizes {
        let _session = crate::kernel::VerificationSession::enter();
        let slices = (0..size)
            .map(|index| {
                pointer(933_000 + index).with_element_count(OldMachineTerm::uint64_constant(2))
            })
            .collect::<Vec<_>>();
        let function = program_function(
            ProgramType::Void,
            "many_slices",
            (0..size)
                .map(|index| {
                    program_parameter(
                        format!("s{index}"),
                        ProgramType::SlicePointer(crate::kernel::SliceElement::Int32),
                    )
                })
                .collect(),
            program_skip(),
        );
        let arguments = slices
            .iter()
            .map(|slice| ProgramExpression::Value(ProgramValue::Pointer(slice.clone())))
            .collect::<Vec<_>>();
        let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::program_function_contract_entry(
                &ExecutionState::new(),
                &function,
                &arguments,
            )
        });
        let entry = entry.unwrap();
        let context = entry
            .facts()
            .iter()
            .fold(PureFactContext::new(), |facts, fact| {
                facts.assume_proposition(fact.proposition().clone())
            });
        let first = slices[0].as_ptr();
        let resources = ResourceContext::new();
        assert!(permits(&first, 8, &context, &resources));
        assert!(!permits(&first, 12, &context, &resources));
        samples.push(work);
    }
    for (size, work) in sizes.iter().zip(&samples) {
        assert!(
            *work as u64 <= samples[0] as u64 * size / sizes[0] + 1_000,
            "slice entry work is not linear in its slice parameters: {samples:?}"
        );
    }
}
