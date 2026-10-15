// Scaling tests of `src/kernel/tests/memory_reasoning_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Unaddressable scalar declarations keep their permissions without growing
/// the observable pointer frame. Addressable locals must remain observable.
#[test]
fn unaddressable_scalar_owners_do_not_restate_observable_memory_frames() {
    let saved = crate::kernel::capture_block_registries();
    let base = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(93_600)),
            },
            0u32.into(),
            1u32.into(),
        )))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(93_601)),
            },
            0u32.into(),
            1u32.into(),
        )));
    let assumptions = PureFactContext::new();
    let expected = base.observable_facts_assuming_valid(&assumptions);
    let mut measured_work = Vec::new();
    for count in [0, 64, 256, 1024] {
        crate::kernel::set_never_address_taken_locals(
            (0..count).map(|i| format!("hidden_{i}")).collect(),
        );
        let mut resources = base.clone();
        for i in 0..count {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    CMemory::local_pointer(&format!("hidden_{i}")),
                    0u32.into(),
                    4u32.into(),
                    1,
                ),
            ));
        }
        let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.observable_facts_assuming_valid(&assumptions)
        });
        assert_eq!(observed, expected);
        measured_work.push((count, work));
        assert_eq!(resources.facts().len(), count + 2);
        let addressed = CResourceFact::own_memory(CMemoryRange::new(
            CMemory::local_pointer("addressed"),
            0u32.into(),
            1u32.into(),
        ));
        let observable = resources
            .unchecked_with_fact(addressed.clone())
            .observable_facts_assuming_valid(&assumptions);
        assert!(observable.iter().any(|fact| matches!(fact, Proposition::CResourceComposition(context) if context.facts().contains(&addressed))));
    }
    crate::kernel::restore_block_registries(&saved);
    assert!(
        measured_work
            .iter()
            .all(|(count, work)| *work <= measured_work[0].1 * 4 + *count * 128 + 32),
        "observable frame projection exceeded bounded work: {measured_work:?}"
    );
}

#[test]
fn memory_range_endpoint_graph_matching_scales_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |id| Bitvector32Term::Variable(Variable(42_000 + id));
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let resource = |index| {
            CResource::Memory(CMemoryRange::new(
                Pointer::symbolic(Variable(43_000)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::add(variable(index), Bitvector32Term::Constant(1)),
            ))
        };
        let left = resource(0);
        let _scope = assumptions.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(c_resources_directly_match(
                    &left,
                    &resource(index),
                    &assumptions,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn loadability_transports_checked_aliases_without_scanning_unrelated_facts() {
    let memory = CMemory::new();
    let storage = Pointer {
        block: "viewed-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let result = Pointer {
        block: PointerBlock::Symbolic(Variable(9_300_100)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(result.clone(), storage.clone()),
        true,
    );
    let view = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: storage.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: result.clone(),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    assert!(
        !PureFactContext::new()
            .assume_proposition(equality.clone())
            .proves(&goal)
    );
    assert!(
        !PureFactContext::new()
            .assume_proposition(view.clone())
            .proves(&goal)
    );
    let samples = [8, 32, 128].map(|size| {
        let mut context = PureFactContext::new()
            .assume_proposition(equality.clone())
            .assume_proposition(view.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: Pointer {
                    block: format!("unrelated-view-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                bytes: Bitvector32Term::Constant(4),
                wide: false,
            });
        }
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| context.proves(&goal));
        assert!(proved);
        assert!(!context.proves(&Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: result.offset_by_bytes(4),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        }));
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "alias transport work: {samples:?}"
    );

    let local = CMemory::local_pointer("expired-view");
    let before = CMemory::new().with_block("local:expired-view", 4);
    let after = before.without_local_block(&local.block);
    let context = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(result.clone(), local.clone()),
            true,
        ))
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: before,
            base: local,
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        });
    assert!(!context.proves(&Proposition::CMemoryLoadable {
        memory: after,
        base: result,
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    }));
}

#[test]
fn memory_loadable_query_ignores_same_block_unrelated_pointer_shapes() {
    let memory = CMemory::new();
    let target = Pointer {
        block: "indexed-viewable-shapes".into(),
        offset: PointerOffsetTerm::Constant(10_000),
    };
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: target.clone(),
                    bytes: Bitvector32Term::Constant(8),
                    wide: false,
                });
            for index in 0..size {
                assumptions = assumptions.assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: Pointer {
                        block: target.block.clone(),
                        offset: PointerOffsetTerm::Constant(index as i64),
                    },
                    bytes: Bitvector32Term::Constant(4),
                    wide: false,
                });
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.proves(&Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: target.clone(),
                    bytes: Bitvector32Term::Constant(4),
                    wide: false,
                })
            });
            assert!(proved);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed viewability query should not inspect unrelated pointer shapes: {samples:?}"
    );
}

#[test]
fn composition_store_separation_uses_checked_aliases_without_scanning_other_owners() {
    use crate::kernel::memory_provenance::owned_composition_store_separated_evidence;

    let parameter = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 4),
    };
    let write_base = parameter(95_001);
    let read = parameter(95_002);
    let owner = Pointer::symbolic(Variable(95_003));
    let alias = ConditionTerm::pointer_equal(write_base.clone(), owner.clone());
    for offset in [0, 8] {
        let write = write_base.offset_by_bytes(offset);
        let mut samples = Vec::new();
        for size in [8, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let resources = (0..size)
                .map(|index| own_memory_fact(parameter(96_000 + index), 0, 1))
                .chain([
                    own_memory_fact(owner.clone(), offset / 4, offset / 4 + 1),
                    own_memory_fact(read.clone(), 0, 1),
                ])
                .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
            let without_alias = PureFactContext::new()
                .assume_proposition(Proposition::CResourceComposition(resources));
            let assumptions = without_alias.clone().assume_condition(alias.clone(), true);
            let (hop, work) = crate::instrumentation::measure_deterministic_work(|| {
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &assumptions)
            });
            let hop = hop.expect("the store's exact alias names its owned member");
            let store = CMemoryDerivation::Store {
                base: crate::kernel::intern_c_memory(CMemory::new()),
                pointer: write.clone(),
                value: int32(7),
            };
            assert!(hop.checks(&store, &read, 4, &assumptions));
            assert!(!hop.checks(&store, &read, 4, &without_alias));
            assert!(!hop.checks(&store, &read, 8, &assumptions));
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &without_alias)
                    .is_none()
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 8, &read, 4, &assumptions)
                    .is_none()
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 8, &assumptions)
                    .is_none()
            );
            let wider_store = CMemoryDerivation::Store {
                base: crate::kernel::intern_c_memory(CMemory::new()),
                pointer: write.clone(),
                value: int64(7),
            };
            assert!(!hop.checks(&wider_store, &read, 4, &assumptions));
            let equal = assumptions.assume_condition(
                ConditionTerm::pointer_equal(write.clone(), read.clone()),
                true,
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &equal).is_none()
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }
}

/// Load equality resolves through a chain of stored cells of any length:
/// each memory's cell holds the load of the next memory's cell, and the
/// chain ends at a constant. Each hop is one memoized query, so the work
/// follows the chain; the alias depth of 64 that used to cut the recursion
/// refused every chain past it.
#[test]
fn load_equality_resolves_through_stored_cell_chains_of_any_length() {
    let base = Pointer {
        block: "chain".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = |index: usize| base.offset_by_elements(Bitvector32Term::Constant(index as u32), 4);
    let mut samples = Vec::new();
    for length in [32usize, 64, 96, 128] {
        let mut memory =
            CMemory::new().store(cell(length), CValue::Int32(Bitvector32Term::Constant(42)));
        for index in (0..length).rev() {
            let next = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(cell(index + 1)),
                crate::kernel::LoadKind::Bits32,
            );
            memory = CMemory::new().store(cell(index), CValue::Int32(next));
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory),
            Box::new(cell(0)),
            crate::kernel::LoadKind::Bits32,
        );
        let (proven, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                &load,
                &Bitvector32Term::Constant(42),
                &PureFactContext::new(),
            )
        });
        assert!(
            proven,
            "a chain of {length} stored cells resolves to its constant"
        );
        samples.push((length, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "load resolution through a cell chain is superlinear: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn shifted_constant_view_extents_match_without_ambient_search() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new();
    let base = Pointer::symbolic(Variable(9_319_000));
    let index = Bitvector32Term::Variable(Variable(9_319_001));
    let count = |length| {
        Bitvector32Term::Subtract(
            Box::new(Bitvector32Term::Add(
                Box::new(index.clone()),
                Box::new(Bitvector32Term::Constant(length)),
            )),
            Box::new(index.clone()),
        )
    };
    let source = |bytes| Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes,
        wide: false,
    };
    for width in [1, 2, 4, 8, 16] {
        let bytes = if width == 1 {
            count(4)
        } else {
            Bitvector32Term::Multiply(
                Box::new(count(4)),
                Box::new(Bitvector32Term::Constant(width)),
            )
        };
        let mut costs = Vec::new();
        for size in [0, 16, 64, 256, 1024] {
            let mut context = PureFactContext::new().assume_proposition(source(bytes.clone()));
            for offset in 0..size {
                context = context.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(9_319_100 + offset)),
                        Bitvector32Term::Constant(offset as u32),
                    ),
                    true,
                );
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.proves_memory_loadable(
                    &memory,
                    &base,
                    &Bitvector32Term::Constant(4 * width),
                )
            });
            assert!(proved);
            costs.push(work);
        }
        assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
        let context = PureFactContext::new().assume_proposition(source(bytes));
        assert!(!context.proves_memory_loadable(
            &memory,
            &base,
            &Bitvector32Term::Constant(4 * width + 1),
        ));
        assert!(!context.proves_memory_loadable(
            &memory,
            &Pointer::symbolic(Variable(9_319_002)),
            &Bitvector32Term::Constant(4 * width),
        ));
    }
    assert!(!PureFactContext::new().proves_memory_loadable(
        &memory,
        &base,
        &Bitvector32Term::Constant(4),
    ));
    let wrapped = Bitvector32Term::Multiply(
        Box::new(count(0x4000_0000)),
        Box::new(Bitvector32Term::Constant(4)),
    );
    assert!(
        !PureFactContext::new()
            .assume_proposition(source(wrapped))
            .proves_memory_loadable(&memory, &base, &Bitvector32Term::Constant(4))
    );
}

#[test]
fn bounded_unsigned_native_indices_project_only_with_full_width_evidence() {
    let native = Bitvector32Term::Variable(Variable(983_110));
    let alias = Bitvector32Term::Variable(Variable(983_111));
    let last = |n| Bitvector32Term::uint64_subtract(n, Bitvector32Term::UInt64Constant(1));
    let wide = |n| PointerOffsetTerm::Int64Scaled {
        value: Box::new(n),
        byte_width: 4,
        unsigned: true,
    };
    let projected = Bitvector32Term::uint32_from_64(last(native.clone()));
    let query = wide(last(alias.clone()));
    let bound = ConditionTerm::uint64_less_equal(
        last(native.clone()),
        Bitvector32Term::UInt64Constant(1_073_741_822),
    );
    let equality = ConditionTerm::uint64_equal(alias.clone(), native.clone());
    let project = |facts: &PureFactContext| {
        crate::kernel::reasoning::element_index_from_offset_with_facts(&query, 4, facts)
    };
    assert_eq!(project(&PureFactContext::new()), None);
    let bounded = PureFactContext::new().assume_condition(bound.clone(), true);
    assert_eq!(project(&bounded), None);
    let equal_only = PureFactContext::new().assume_condition(equality.clone(), true);
    assert_eq!(project(&equal_only), None);
    let low_bound = ConditionTerm::signed_less_equal(
        projected.clone(),
        Bitvector32Term::Constant(1_073_741_822),
    );
    assert_eq!(
        project(&equal_only.clone().assume_condition(low_bound, true)),
        None
    );
    let signed_bound = ConditionTerm::int64_signed_less_equal(
        last(native.clone()),
        Bitvector32Term::Int64Constant(1_073_741_822),
    );
    assert_eq!(
        project(&equal_only.clone().assume_condition(signed_bound, true)),
        None
    );
    let mut measured = Vec::new();
    for count in [0, 8, 64, 512] {
        let mut facts = bounded.clone().assume_condition(equality.clone(), true);
        for i in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_equal(
                    Bitvector32Term::Variable(Variable(984_000 + i)),
                    Bitvector32Term::UInt64Constant(7),
                ),
                true,
            );
        }
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| project(&facts));
        assert_eq!(answer, Some(projected.clone()));
        measured.push(work);
        assert!(facts.element_index_rebuild_is_exact_for_width(&query, 4));
        // Element projection is exact even though scaling the largest index
        // exceeds the signed byte word. It grants no unbounded byte projection.
        assert!(!facts.element_index_rebuild_is_exact_for_width(&query, 1));
    }
    assert!(
        measured.windows(2).all(|pair| pair[0] == pair[1]),
        "{measured:?}"
    );
    for value in [0, 1_073_741_823, 1u64 << 32, u64::MAX] {
        let actual = value.wrapping_sub(1);
        let offset = wide(last(Bitvector32Term::UInt64Constant(value)));
        let answer = crate::kernel::reasoning::element_index_from_offset_with_facts(
            &offset,
            4,
            &PureFactContext::new(),
        );
        assert_eq!(
            answer,
            i32::try_from(actual)
                .ok()
                .map(|x| Bitvector32Term::Constant(x as u32))
        );
    }
}
