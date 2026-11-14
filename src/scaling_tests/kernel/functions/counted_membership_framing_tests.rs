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
    let memory = Memory::new().with_block("counter", 4);
    let ordinary = |name: String, next: Option<String>| {
        CompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            next.into_iter()
                .map(|next| {
                    ResourceSpec::composite(
                        ResourceAccessMode::Own,
                        next,
                        vec![c_variable("p")],
                        vec![ProgramType::Int32Pointer],
                    )
                })
                .collect(),
            vec![],
        )
    };
    let population = || {
        CompositeResourceDefinition::authority_control(
            "z-count",
            vec![c_parameter("p", ProgramType::Int32Pointer)],
            None,
            vec![ResourceSpec::owned_memory(MemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![],
        )
    };
    let root = |name: &str| {
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_composite(
            name.into(),
            vec![ProgramValue::pointer(pointer.clone())],
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
            residual.unchecked_with_fact(ResourceFact::own_composite(
                "boxed".into(),
                vec![ProgramValue::pointer(object(index))],
            ))
        });
        let memory = Memory::new();
        let assumptions = PureFactContext::new();
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context(residual.clone());
        let written = MemoryRange::new(
            object(size + 1),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
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
                MachineTerm::Variable(Variable(783_000 + index)),
                4,
            ),
        };
        let residual = (0..size).fold(ResourceContext::new(), |resources, index| {
            resources.unchecked_with_fact(ResourceFact::own_composite(
                "boxed".into(),
                vec![ProgramValue::pointer(object(index))],
            ))
        });
        let cell = object(size + 1);
        let written = MemoryRange::new(
            cell.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        );
        let original = residual
            .clone()
            .unchecked_with_fact(ResourceFact::own_memory(written.clone()));
        let memory = Memory::new();
        let assumptions = PureFactContext::new();
        let state = ExecutionState::new()
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

#[test]
fn call_frame_preparation_ignores_unrelated_retained_instances() {
    let samples = [4_u64, 16, 64].map(|size| {
        let _session = VerificationSession::enter();
        let schema = ResourceFieldSchema::new(vec![(
            "tag".into(),
            ResourceFieldType::C(ProgramType::Int32),
        )])
        .unwrap();
        let residual = (0..size).fold(ResourceContext::new(), |resources, index| {
            resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(
                ResourceInstance::new(
                    Variable(8_600_000 + index),
                    "boxed".into(),
                    vec![
                        ProgramValue::pointer(Pointer::symbolic(Variable(8_610_000 + index)))
                            .into(),
                    ]
                    .into(),
                    schema.clone(),
                    vec![int32(0).into()].into(),
                )
                .unwrap(),
            )))
        });
        let assumptions = PureFactContext::new();
        let state = ExecutionState::new().with_resource_context(residual.clone());
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast = crate::kernel::search::FastOperationScope::enter(
                "call frame retaining opaque instances",
            );
            call_kept_ownership(
                &residual,
                &[boxed_definition().with_instance_schema(Some(schema.clone()))],
                &state,
                &assumptions,
            )
        });
        work
    });
    eprintln!("call frame preparation: {samples:?}");
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

/// One fixed call effect must not open every unrelated
/// retained composite. Setup, havoc and subsequent observation are outside the meter.
/// Exercise both a nested body and a body whose bound reads memory; neither
/// qualifies for the argument-direct shortcut.
#[test]
fn call_frame_preparation_must_not_open_unrelated_composites() {
    let mut curves = Vec::new();
    for memory_bound in [false, true] {
        let samples = [4_u64, 16, 64].map(|size| {
            let _session = VerificationSession::enter();
            let object = |index| Pointer::symbolic(Variable(8_700_000 + index));
            let body = if memory_bound {
                vec![
                    ResourceSpec::owned_memory(MemorySegment::new(
                        c_variable("length"),
                        c_int32_literal(0),
                        c_int32_literal(1),
                    )),
                    ResourceSpec::owned_memory(MemorySegment::new(
                        c_variable("p"),
                        c_int32_literal(0),
                        c_load(c_variable("length")),
                    )),
                ]
            } else {
                vec![ResourceSpec::composite(
                    ResourceAccessMode::Own,
                    "boxed".into(),
                    vec![c_variable("p")],
                    vec![ProgramType::Int32Pointer],
                )]
            };
            let wrapper = CompositeResourceDefinition::new(
                "wrapper",
                vec![
                    c_parameter("p", ProgramType::Int32Pointer),
                    c_parameter("length", ProgramType::Int32Pointer),
                ],
                None,
                false,
                body,
                vec![],
            );
            assert!(!wrapper.has_argument_direct_body());
            let definitions = [boxed_definition(), wrapper];
            let mut residual = ResourceContext::new();
            let mut memory = Memory::new();
            for index in 0..size {
                residual = residual.unchecked_with_fact(ResourceFact::own_composite(
                    "wrapper".into(),
                    vec![
                        ProgramValue::pointer(object(index)),
                        ProgramValue::pointer(object(1_000 + index)),
                    ],
                ));
                memory = memory.store(object(1_000 + index), int32(1));
            }
            let assumptions = PureFactContext::new();
            let state = ExecutionState::new()
                .with_memory(memory.clone())
                .with_resource_context(residual.clone());
            // The callee's effect and the observed retained cell are fixed at
            // all sizes. Every added wrapper is unrelated to either one.
            let written = MemoryRange::new(object(2_000), 0u32.into(), 1u32.into());
            let (kept, work) = crate::instrumentation::measure_deterministic_work(|| {
                call_kept_ownership(&residual, &definitions, &state, &assumptions)
            });
            let opened = kept.opened_resources_for_test().facts().len();
            let after = memory.with_call_memory_havoc(
                Variable(8_710_000),
                std::slice::from_ref(&written),
                &assumptions,
                Some(&kept),
            );
            assert_eq!(
                opened, 0,
                "opaque composites contribute no discovered ranges"
            );
            assert!(CallKeptRanges::recorded_on(&after).is_none());
            work
        });
        eprintln!("memory_bound={memory_bound}, sizes=[4,16,64], call framing work={samples:?}");
        curves.push(samples);
    }
    for samples in curves {
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "fixed call framing opens unrelated composites: {samples:?}"
        );
    }
}
