// Scaling tests of `src/kernel/primitives/memory_equality_index.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// The selection charges the same work beside 2, 4, 8 and 16 unrelated
/// framed ranges as beside 1,024 (1,118 units at 16 to 1,024 on
/// 2026-10-15), so an ambient scan shows as growth at these sizes; the
/// larger sizes cost seconds of setup in a debug build, nearly all of it in
/// `synchronize_memory_equalities` over the unrelated ranges.
#[test]
fn checked_read_endpoint_selects_framed_ranges_without_ambient_scan() {
    let mut samples = Vec::new();
    for size in [2u32, 4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CMemory::new();
        let read = |context: &PureFactContext, memory: &CMemory, address: &Pointer| {
            let snapshot = crate::kernel::intern_c_memory_ref(memory);
            let variable = crate::kernel::load_variable_for_cell_with_origin(
                &snapshot,
                address,
                LoadKind::Bits32,
                C_POINTER_BYTE_WIDTH,
                &snapshot,
            );
            let pointer = Pointer::loaded(
                address.block.clone(),
                Bitvector32Term::Variable(variable),
                4,
            );
            context.register_pointer_read(&pointer, &snapshot, address);
            pointer
        };
        let source = read(&PureFactContext::new(), &before, &field);
        // Match the contract's complete pointer-valued descriptor cell.
        // Its unknown value is retained as the initial opaque read.
        let before = before.store(
            field.clone(),
            CValue::Pointer(CPointerValue::new(source.clone(), CType::Int32Pointer)),
        );
        let count = Bitvector32Term::Variable(Variable(999_321));
        let range =
            |base| CMemoryRange::new_with_element_width(base, 0u32.into(), count.clone(), 4);
        let field_range =
            CMemoryRange::new_with_element_width(field.clone(), 0u32.into(), 2u32.into(), 4);
        let separation = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(field_range.clone())),
            right: Box::new(CResource::Memory(range(source.clone()))),
        };
        let context = PureFactContext::new()
            .assume_proposition(separation.clone())
            .assume_condition(
                ConditionTerm::signed_less_equal(2u32.into(), count.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(count.clone(), 1000u32.into()),
                true,
            );
        let held = CResourceFact::own_memory(range(source.clone()));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::view_memory(field_range))
            .unchecked_with_fact(held.clone());
        for index in 0..size {
            let unrelated = read(&context, &before, &field.offset_by_bytes(64 + index * 8));
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(range(unrelated)));
        }
        resources.synchronize_memory_equalities(&context);
        let local = Pointer {
            block: PointerBlock::Concrete("local:frame-counter".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let after = before
            .clone()
            .with_block(local.block.clone(), 4)
            .store(source.offset_by_bytes(4), CValue::Int32(7u32.into()))
            .store(local, CValue::Int32(8u32.into()));
        let current = read(&context, &after, &field);
        let weakened = context.without_exact_fact(&separation);
        let required = CResourceFact::own_memory(range(current.clone()));
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .directly_supporting_fact(&required, &context)
                .cloned()
        });
        assert_eq!(found, Some(held.clone()), "size={size}, work={work}");
        assert!(work < 2000, "size={size}, work={work}");
        samples.push(work);
        assert_eq!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(&current, &context),
            Some(source.clone()),
            "the complete-cell certificate must recover this exact stored value",
        );
        assert!(!context.equality_graph.are_equal(&source, &current));
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &context)
                .is_some()
        );
        assert!(
            resources
                .directly_supporting_fact(&required, &weakened)
                .is_none()
        );
        let withdrawn = resources
            .clone()
            .without_exact_representation(&held)
            .unwrap();
        assert!(
            withdrawn
                .directly_supporting_fact(&required, &context)
                .is_none()
        );
        let partial = after.store(field.offset_by_bytes(4), CValue::Int32(9u32.into()));
        let changed = CResourceFact::own_memory(range(read(&context, &partial, &field)));
        assert!(
            resources
                .directly_supporting_fact(&changed, &context)
                .is_none()
        );
        assert!(
            resources
                .without_fact_incrementally(&changed, &context)
                .is_none()
        );
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "the checked read's selection read unrelated framed ranges: {samples:?}"
    );
}

#[test]
fn wide_read_keeps_full_buffer_index_beside_a_batch_cursor() {
    let mut samples = Vec::new();
    for count in [0_u64, 16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(989_200)), 1),
        };
        let prefix = Bitvector32Term::Variable(Variable(989_201));
        let local = Bitvector32Term::Variable(Variable(989_202));
        let full = Bitvector32Term::Variable(Variable(989_203));
        let batch = Pointer::symbolic(Variable(989_204));
        let query = Pointer::symbolic(Variable(989_205));
        let global = base.offset_by_typed_elements(full.clone(), 1, true, true);
        let mut aliases = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_equal(
                    batch.clone(),
                    base.offset_by_typed_elements(prefix, 1, true, true),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_elements(Bitvector32Term::Variable(Variable(989_206)), 1),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_typed_elements(local, 1, true, true),
                ),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), global), true);
        for i in 0..count {
            aliases = aliases.assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_elements(Bitvector32Term::Variable(Variable(990_000 + i)), 1),
                ),
                true,
            );
        }
        let facts = aliases.clone().assume_condition(
            ConditionTerm::uint64_less_than(full.clone(), Bitvector32Term::UInt64Constant(22208)),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_wide(
                base.clone(),
                Bitvector32Term::UInt64Constant(0),
                Bitvector32Term::UInt64Constant(22208),
                1,
            ),
        ));
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&query, 1, &facts)
        });
        assert!(
            permitted,
            "alignment: {:?}",
            resources
                .read_access_entries(&query, 1, &facts)
                .map(|c| c.index.graph.pointer_at_base_with_wide_index(&query, &base))
        );
        samples.push(work);
        assert!(!resources.permits_memory_read(&query, 2, &facts));
        assert!(!resources.permits_memory_read(&query, 1, &aliases));
        let boundary = aliases.assume_condition(
            ConditionTerm::uint64_equal(full, Bitvector32Term::UInt64Constant(22208)),
            true,
        );
        assert!(!resources.permits_memory_read(&query, 1, &boundary));
        assert!(!ResourceContext::new().permits_memory_read(&query, 1, &facts));
    }
    assert!(
        samples[4] <= samples[1] * 3 + 128,
        "batch read alignment scanned aliases: {samples:?}"
    );
}

#[test]
fn wide_read_keeps_native_index_beside_a_narrow_alias() {
    let mut samples = Vec::new();
    for count in [16_u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let bytes = Pointer::symbolic(Variable(986_000));
        let alternate = Pointer::symbolic(Variable(986_001));
        let native_index = Bitvector32Term::Variable(Variable(986_002));
        let narrow = alternate.offset_by_elements(Bitvector32Term::Variable(Variable(986_003)), 1);
        let wide = bytes.offset_by_typed_elements(native_index.clone(), 1, true, true);
        let query = Pointer::symbolic(Variable(986_004));
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), narrow), true)
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), wide), true)
            .assume_condition(
                ConditionTerm::uint64_less_than(
                    native_index.clone(),
                    Bitvector32Term::UInt64Constant(15),
                ),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_wide(
                bytes,
                Bitvector32Term::UInt64Constant(0),
                Bitvector32Term::UInt64Constant(15),
                1,
            ),
        ));
        for item in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(987_000 + item)),
                    query.clone(),
                ),
                true,
            );
        }
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&query, 1, &facts)
        });
        assert!(
            permitted,
            "native bounds remain available beside a narrow alias"
        );
        assert!(!resources.permits_memory_read(&query, 2, &facts));
        assert!(!ResourceContext::new().permits_memory_read(&query, 1, &facts));
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] * 3 + 128,
        "native read alignment scanned its address class: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn constant_base_interior_lookup_scales_with_selected_range() {
    let mut samples = Vec::new();
    for count in [16_u32, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(950_000));
        let model = Pointer::symbolic(Variable(950_001));
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(950_002)), 4),
        };
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(950_003)), 4),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(950_004)), 4),
        };
        let prefix = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(parameter, parent), true)
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_facts((0..count).map(|index| {
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                model.clone(),
                (index * 8 + 2).into(),
                (index * 8 + 6).into(),
                4,
            ))
        }));
        resources.synchronize_memory_equalities(&prefix);
        // A late base alias must update the indexed payload, not force a
        // search through all the other spans relative to that same base.
        let facts = prefix
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), old_read), true)
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), model), true);
        resources.synchronize_memory_equalities(&facts);
        let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            cursor.clone(),
            4u32.into(),
            6u32.into(),
            4,
        ));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .clone()
                .without_fact_incrementally(&required, &facts)
        });
        assert!(remaining.is_some());
        assert!(resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts));
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &prefix)
                .is_none()
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "interior lookup grew faster than indexed paths: {samples:?}"
    );
    assert!(
        samples[3] <= samples[0] * 3,
        "interior lookup followed unrelated same-base spans: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn modeled_pointer_alias_field_lookup_scales_with_selected_addresses() {
    let mut previous = None;
    for count in [16_u32, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(940_000));
        let model = Pointer::symbolic(Variable(940_001));
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(940_002)), 4),
        };
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(940_003)), 4),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(940_004)), 4),
        };
        let prefix = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(parameter, parent), true)
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_facts((0..count).map(|index| {
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                old_read.offset_by_bytes(index * 16),
                0u32.into(),
                1u32.into(),
                8,
            ))
        }));
        resources.synchronize_memory_equalities(&prefix);
        // Publish the cursor alias after the suppliers. Only address
        // applications affected by this equality may be reindexed.
        let facts = prefix
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(cursor.clone(), old_read.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), model), true);
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts)
        });
        assert!(permitted);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "selected-address work changed with {count} suppliers"
            );
        }
        previous = Some(work);
        assert!(!resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &prefix));
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn mixed_extent_read_hits_and_misses_do_not_scan_unrelated_ranges() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024] {
        let base = Pointer::symbolic(Variable(851_030));
        let alias = Pointer::symbolic(Variable(851_031));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 4))
            .unchecked_with_fact(view(&base, 1, 2));
        for index in 1..=size {
            resources =
                resources.unchecked_with_fact(view(&base, index * 8, index * 8 + 1 + index % 2));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let facts = empty.assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |offset| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    resources
                        .concrete_read_entries(&at(2), 2, &facts)
                        .unwrap()
                        .count(),
                    1
                );
                assert!(resources.permits_memory_read(&at(2), 2, &facts));
                assert!(!resources.permits_memory_read(&at(4), 1, &facts));
                assert!(!resources.permits_memory_read(&at(2), 3, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "read checker scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "interval lookup scanned unrelated ranges: {samples:?}"
    );
}

#[test]
fn a_read_does_not_materialize_all_covering_views() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024] {
        let base = Pointer::symbolic(Variable(851_040));
        let facts = PureFactContext::new();
        let mut resources = ResourceContext::new();
        for end in 1..=size {
            resources = resources.unchecked_with_fact(view(&base, 0, end));
        }
        resources.synchronize_memory_equalities(&facts);
        let (allowed, work) = crate::persistent::measure_persistent_work(|| {
            resources.permits_memory_read(&base, 1, &facts)
        });
        assert!(allowed);
        samples.push((size, work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "a read enumerated every covering view: {samples:?}"
    );
}
