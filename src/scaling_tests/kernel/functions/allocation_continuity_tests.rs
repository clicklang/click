// Scaling tests of `src/kernel/functions.rs` (module `allocation_continuity_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// An allocating call beside N live objects the caller keeps folded
/// (`boxed(p_j)`, one heap block each) must not expand them: none can
/// expose, continue or be left stale by an allocation the call did not
/// consume (`roadmap/scaling.md`).
#[test]
fn allocating_call_does_not_expand_the_callers_kept_objects() {
    let boxed = program_function(
        ProgramType::Void,
        "unused",
        vec![],
        program_return(program_void_value()),
    )
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "boxed",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![],
    )]);
    let interface = boxed.contract_interface();
    let heap = |id: u64| Address {
        base: AddressBase::Heap(id),
        offset: AddressOffset::Constant(0),
    };
    let bytes = MachineTerm::constant(4);
    let samples = [16, 64, 256]
        .into_iter()
        .map(|size| {
            let mut memory = SymbolicMemory::new();
            let mut kept = ResourceContext::new();
            for index in 0..size {
                let object = heap(931_000 + index as u64);
                memory = memory
                    .with_heap_allocation_claim(
                        object.clone(),
                        AllocationSize::int32(bytes.clone()),
                    )
                    .expect("a fresh live object");
                kept = kept.unchecked_with_fact(ResourceFact::own_composite(
                    "boxed".into(),
                    vec![ProgramValue::pointer(object)],
                ));
            }
            let created = heap(932_000);
            let output = ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_allocation(created.clone(), bytes.clone()));
            let state = ExecutionState::new().with_memory(memory.clone());
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                apply_verified_heap_allocation_delta(
                    memory.clone(),
                    &memory,
                    &ResourceContext::new(),
                    &kept,
                    &output,
                    interface,
                    &PureFactContext::new(),
                    None,
                    &state,
                    &state,
                )
            });
            let VerifiedAllocationDelta {
                memory: after,
                retired_allocations: retired,
                ..
            } = result.expect("an allocating call");
            assert!(retired.is_empty());
            assert!(after.live_heap_block_size(&created).is_some());
            (size, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(2)),
        "an allocating call's delta grows with the caller's kept objects: {samples:?}"
    );
}

#[test]
fn allocation_size_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| MachineTerm::Variable(Variable(id));
        let offset = |value| MachineTerm::add(value, MachineTerm::constant(1));
        let base = external_pointer(930_020);
        let input_size = offset(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let output_size = offset(var(index));
                assert_eq!(
                    allocation_continuity(
                        &base,
                        &AllocationSize::int32(input_size.clone()),
                        &base,
                        &AllocationSize::int32(output_size),
                        &context,
                    ),
                    AllocationContinuity::Same,
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

/// [`allocation_size_graph_queries_scale_without_fact_index`] with 64-bit
/// sizes: continuity of two `uint64` byte counts made equal by a chain of
/// `size` facts is answered by the 64-bit equality graph, without visiting
/// the fact index, in work linear in the queries.
#[test]
fn uint64_allocation_size_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| MachineTerm::Variable(Variable(id));
        let allocation_size = |value| {
            AllocationSize::new(
                MachineTerm::uint64_add(value, MachineTerm::uint64_constant(1)),
                AllocationSizeKind::UInt64,
            )
        };
        let base = external_pointer(930_030);
        let input_size = allocation_size(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(var(index), var(index + 1)),
                true,
            );
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let output_size = allocation_size(var(index));
                assert_eq!(
                    allocation_continuity(&base, &input_size, &base, &output_size, &context,),
                    AllocationContinuity::Same,
                );
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn allocation_companion_alias_lookup_ignores_unrelated_storage_and_alias_stars() {
    for hit in [false, true] {
        let mut work = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let _session = VerificationSession::enter();
            let (base, caller, callee) = allocation_companion_call(size);
            let mut facts = PureFactContext::new();
            for id in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        base.clone(),
                        Address::symbolic(Variable(10_000_000 + id)),
                    ),
                    true,
                );
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        Address::symbolic(Variable(20_000_000 + id)),
                        Address::symbolic(Variable(30_000_000 + id)),
                    ),
                    true,
                );
            }
            let alias = Address::symbolic(Variable(if hit {
                10_000_000 + size - 1
            } else {
                40_000_000
            }));
            let output = ResourceFact::own_allocation(alias, 4);
            let (returned, measured) = crate::instrumentation::measure_deterministic_work(|| {
                transfer_population_call_facts(
                    callee.clone(),
                    &callee,
                    &caller,
                    &callee,
                    std::iter::once(&output),
                    &[],
                    &facts,
                )
                .unwrap()
            });
            let finished = returned
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .finish_call(caller.population_effects.creation.as_ref().unwrap());
            assert_eq!(finished.is_ok(), hit);
            work.push(measured);
        }
        assert!(
            work.iter().max().unwrap() <= &(work[0] + 80),
            "hit={hit}, alias and storage growth changed one return transfer: {work:?}"
        );
    }
}
