// Scaling tests of `src/kernel/functions.rs` (module `counted_membership_framing_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn independent_body_expansion_indexes_definitions_and_walks_depth_once() {
    let pointer = Pointer {
        block: "counter".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new();
    let memory = CMemory::new().with_block("counter", 4);
    let ordinary = |name: String, next: Option<String>| {
        CCompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            next.into_iter()
                .map(|next| {
                    CResourceSpec::composite(
                        CResourceAccessMode::Own,
                        next,
                        vec![c_variable("p")],
                        vec![CType::Int32Pointer],
                    )
                })
                .collect(),
            vec![],
        )
    };
    let population = || {
        CCompositeResourceDefinition::authority_control(
            "z-count",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![],
        )
    };
    let root = |name: &str| {
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
            name.into(),
            vec![CValue::pointer(pointer.clone())],
        ))
    };
    let mut depth_samples = Vec::new();
    for depth in [16, 32, 64] {
        let mut definitions = (0..depth)
            .map(|index| {
                ordinary(
                    format!("wrapper-{index:04}"),
                    Some(if index + 1 == depth {
                        "z-count".into()
                    } else {
                        format!("wrapper-{:04}", index + 1)
                    }),
                )
            })
            .collect::<Vec<_>>();
        definitions.push(population());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let expanded = expand_composites_for_frame(
                &root("wrapper-0000"),
                &definitions,
                &memory,
                &assumptions,
            )
            .unwrap();
            assert!(owned_memory_ranges_of(&expanded).is_empty());
            assert_eq!(expanded.facts().len(), 1);
        });
        depth_samples.push(work);
    }
    assert!(
        depth_samples[2] <= depth_samples[0] * 7 + 128,
        "nested expansion rescans its ancestors: {depth_samples:?}"
    );
    let mut frame_samples = Vec::new();
    for size in [16, 64, 256] {
        let mut definitions = (0..size)
            .map(|index| ordinary(format!("unrelated-{index:04}"), None))
            .collect::<Vec<_>>();
        definitions.push(population());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let expanded =
                expand_composites_for_frame(&root("z-count"), &definitions, &memory, &assumptions)
                    .unwrap();
            assert!(owned_memory_ranges_of(&expanded).is_empty());
        });
        frame_samples.push(work);
    }
    for pair in frame_samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 16,
            "selected body scans unrelated definitions: {frame_samples:?}"
        );
    }
}

/// A call keeps the memory of every held argument-direct composite without
/// opening one: recording the kept memory costs the same beside 16, 64 or
/// 256 of them, and a question about one composite's cell opens only it.
#[test]
fn a_call_keeps_argument_direct_composites_in_work_independent_of_their_number() {
    let mut recording = Vec::new();
    let mut asking = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let object = |index: u64| Pointer::symbolic(Variable(782_000 + index));
        let residual = (0..size).fold(ResourceContext::new(), |residual, index| {
            residual.unchecked_with_fact(CResourceFact::own_composite(
                "boxed".into(),
                vec![CValue::pointer(object(index))],
            ))
        });
        let memory = CMemory::new();
        let assumptions = PureFactContext::new();
        let state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(residual.clone());
        let written = CMemoryRange::new(
            object(size + 1),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            let kept = call_kept_ownership(&residual, &[boxed_definition()], &state, &assumptions);
            memory.with_call_memory_havoc(Variable(782_900), &[written], &assumptions, Some(&kept))
        });
        recording.push(work);
        let recorded = CallKeptRanges::recorded_on(&after).expect("kept memory is recorded");
        let (kept, work) = crate::instrumentation::measure_deterministic_work(|| {
            recorded.holds_access(&object(size / 2), 4, &assumptions)
        });
        assert!(kept, "size {size}");
        asking.push(work);
    }
    for (name, work) in [("recording", &recording), ("asking", &asking)] {
        assert!(
            work.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "{name} kept memory grows with the held composites: {work:?}"
        );
    }
}

/// The callee borrowed a flat cell. Unchanged caller composites cannot own
/// that same cell, even when their symbolic arguments share its block.
#[test]
fn a_transferred_flat_cell_does_not_open_unrelated_kept_composites() {
    let mut samples = Vec::new();
    let mut recording = Vec::new();
    for size in [2u64, 4, 8, 16] {
        let _session = VerificationSession::enter();
        let object = |index: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(783_000 + index)),
                4,
            ),
        };
        let residual = (0..size).fold(ResourceContext::new(), |resources, index| {
            resources.unchecked_with_fact(CResourceFact::own_composite(
                "boxed".into(),
                vec![CValue::pointer(object(index))],
            ))
        });
        let cell = object(size + 1);
        let written = CMemoryRange::new(
            cell.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let original = residual
            .clone()
            .unchecked_with_fact(CResourceFact::own_memory(written.clone()));
        let memory = CMemory::new();
        let assumptions = PureFactContext::new();
        let state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context(original);
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            let kept = call_kept_ownership(&residual, &[boxed_definition()], &state, &assumptions)
                .with_caller_before_transfer(state.resources());
            memory.with_call_memory_havoc(Variable(783_900), &[written], &assumptions, Some(&kept))
        });
        recording.push(work);
        let recorded = CallKeptRanges::recorded_on(&after).unwrap();
        let (held, work) = crate::instrumentation::measure_deterministic_work(|| {
            recorded.holds_access(&cell, 4, &assumptions)
        });
        assert!(!held);
        samples.push(work);
    }
    assert!(
        recording.iter().all(|work| *work <= recording[0] + 128),
        "recording a caller frame scans unrelated composites: {recording:?}"
    );
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "unrelated caller composites are opened for a transferred flat cell: {samples:?}"
    );
}
