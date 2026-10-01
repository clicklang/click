use super::*;

fn view(base: &Pointer, start: u32, end: u32) -> CResourceFact {
    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        base.clone(),
        start.into(),
        end.into(),
        1,
    ))
}

#[test]
fn cell_index_follows_completed_pointer_reads_and_preserves_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new();
    let snapshot = crate::kernel::intern_c_memory(memory.clone());
    let (a, b) = (
        Pointer::symbolic(Variable(852_010)),
        Pointer::symbolic(Variable(852_011)),
    );
    let read = |address: &Pointer| {
        let paths = crate::kernel::eval::evaluate_c_memory_load_paths(
            &memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new(),
            Vec::new(),
            &PureFactContext::new(),
            true,
            false,
            None,
            None,
        );
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
            panic!("pointer read")
        };
        (value.pointer().clone(), paths[0].facts.clone())
    };
    let (x, xf) = read(&a);
    let (y, yf) = read(&b);
    let facts = xf
        .iter()
        .chain(&yf)
        .fold(PureFactContext::new(), |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
    let cell = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        x.clone(),
        0u32.into(),
        4u32.into(),
        1,
    ));
    let resources = ResourceContext::new().unchecked_with_fact(cell.clone());
    resources.synchronize_memory_equalities(&facts);
    let sibling = resources.clone();
    let connected = facts
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    // Resource lookup must register retained read definitions itself. A prior
    // pointer-equality query must not be needed to warm the graph.
    assert!(
        resources
            .concrete_read_entries(&y, 4, &connected)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&y, 4, &connected));
    assert!(
        resources
            .concrete_write_entries(&y, 4, &connected)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&y, 4, &connected),
        cell.memory_own_range()
    );
    assert!(!sibling.permits_memory_read(&y, 4, &facts));
    assert!(sibling.memory_write_range(&y, 4, &facts).is_none());
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(4), 4, &connected));
    let old = Pointer::loaded_value(&snapshot, &a);
    assert!(
        resources
            .concrete_read_entries(&old, 4, &connected)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&old, 4, &connected));
    assert!(
        resources
            .concrete_write_entries(&old, 4, &connected)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&old, 4, &connected),
        cell.memory_own_range()
    );
    let later = crate::kernel::intern_c_memory(memory.with_block("later", 8));
    assert!(!resources.permits_memory_read(&Pointer::loaded_value(&later, &a), 4, &connected));
    assert!(
        resources
            .memory_write_range(&Pointer::loaded_value(&later, &a), 4, &connected)
            .is_none()
    );
    assert!(resources.memory_write_range(&y, 5, &connected).is_none());
    let removed = resources
        .clone()
        .without_exact_representation(&cell)
        .unwrap();
    assert!(!removed.permits_memory_read(&y, 4, &connected));
    assert!(removed.memory_write_range(&y, 4, &connected).is_none());
    let restored = removed.unchecked_with_fact(cell).normalized(&connected);
    assert!(restored.permits_memory_read(&y, 4, &connected));
    assert!(restored.memory_write_range(&y, 4, &connected).is_some());
}

#[test]
fn typed_cell_candidates_follow_raw_offset_syntax_and_check_ownership() {
    let var = |id| PointerOffsetTerm::Variable(Variable(id));
    let raw = PointerOffsetTerm::Add(Box::new(var(852_022)), Box::new(var(852_021)));
    let (owner, alias) = (
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: raw.clone(),
        },
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: var(852_023),
        },
    );
    let cell = |base| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            1u32.into(),
            4,
        ))
    };
    let resources = ResourceContext::new().unchecked_with_fact(cell(owner.clone()));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(raw, alias.offset.clone()),
        true,
    );
    assert!(
        resources
            .concrete_read_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(
        resources
            .concrete_write_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&alias, 4, &facts),
        cell(owner.clone()).memory_own_range()
    );
    let entries =
        resources.equal_address_entries(cell(alias.clone()).memory_range().unwrap(), true, &facts);
    assert_eq!(entries.len(), 1);
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&cell(alias.clone()), &facts)
            .is_some()
    );
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&cell(alias.clone()), &empty)
            .is_none()
    );
    let view_only = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
    assert!(view_only.permits_memory_read(&alias, 4, &facts));
    assert!(view_only.memory_write_range(&alias, 4, &facts).is_none());
    assert!(
        view_only
            .without_fact_incrementally(&cell(alias), &facts)
            .is_none()
    );
}

#[test]
fn whole_cell_write_merges_and_queries_do_not_scan_other_payloads() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(862_000 + id)),
        };
        let owner = CResourceFact::own_memory(CMemoryRange::new(at(0), 0u32.into(), 1u32.into()));
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for i in 0..size {
            // Large footprint payload at the alias, plus unrelated owners.
            resources = resources
                .unchecked_with_fact(view(&at(1), 0, 8 + i as u32 * 4))
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    at(i + 2),
                    0u32.into(),
                    1u32.into(),
                )));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let ((facts, merge_work), merge_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let facts = empty.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(1).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    facts
                })
            });
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for bytes in [4, C_POINTER_BYTE_WIDTH] {
                    let entries = resources
                        .concrete_write_entries(&at(1), bytes, &facts)
                        .unwrap();
                    assert!(entries.exact());
                    assert_eq!(entries.count(), 1);
                    assert_eq!(
                        resources.memory_write_range(&at(1), bytes, &facts),
                        owner.memory_own_range()
                    );
                }
            })
        });
        samples.push((size, merge_work, merge_map_work, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32 && samples[3].3 <= samples[0].3 * 2 + 32,
        "write merge/query scanned other payloads: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128 && samples[3].4 <= samples[0].4 * 3 + 128,
        "write merge/query rebuilt other payloads: {samples:?}"
    );
}

#[test]
fn late_offset_cell_hits_scale_with_affected_entries() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(853_000 + id)),
        };
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let ((facts, update_work), update_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let facts = empty.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(size).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    facts
                })
            });
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    resources
                        .concrete_read_entries(&at(size), 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(resources.permits_memory_read(&at(size), 4, &facts));
            })
        });
        samples.push((size, update_work, update_map_work, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "merge scanned unrelated cells: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "merge scanned unrelated map: {samples:?}"
    );
    assert!(
        samples[3].3 <= samples[0].3 * 2 + 32,
        "query scanned unrelated cells: {samples:?}"
    );
    assert!(
        samples[3].4 <= samples[0].4 * 3 + 128,
        "query scanned unrelated map: {samples:?}"
    );
}

#[test]
fn cell_publication_and_forks_do_not_repeat_input_registration() {
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(854_000 + id)),
        };
        let mut resources = ResourceContext::new();
        let mut facts = PureFactContext::new();
        resources.synchronize_memory_equalities(&facts);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
                    resources.synchronize_memory_equalities(&facts);
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(i).offset, at(size + i).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    assert!(resources.permits_memory_read(&at(size + i), 4, &facts));
                }
                for i in 0..size {
                    let branch_resources = resources.clone();
                    let branch_facts = facts.clone().assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(3 * size + i).offset),
                        true,
                    );
                    branch_resources.synchronize_memory_equalities(&branch_facts);
                    assert!(
                        branch_resources
                            .concrete_read_entries(&at(3 * size + i), 4, &branch_facts)
                            .unwrap()
                            .exact()
                    );
                    assert!(branch_resources.permits_memory_read(
                        &at(3 * size + i),
                        4,
                        &branch_facts
                    ));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work <= 800 * size as usize, "size={size}, work={work}");
        assert!(
            map_work <= 4096 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn unspellable_affine_shifts_cannot_produce_decisive_cell_misses() {
    let owner = Pointer::symbolic(Variable(855_000));
    let alias = Pointer::symbolic(Variable(855_001));
    let x = PointerOffsetTerm::Variable(Variable(855_002));
    let displaced = Pointer {
        block: alias.block.clone(),
        offset: PointerOffsetTerm::Add(Box::new(x.clone()), Box::new(x)),
    };
    let resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    // Keep the alias block representative so the indexed owner must move
    // by 2*x, which AffineOffset::to_offset_term does not spell.
    let mut facts = empty;
    for i in 3..8 {
        facts = facts.assume_condition(
            ConditionTerm::pointer_equal(alias.clone(), Pointer::symbolic(Variable(855_000 + i))),
            true,
        );
    }
    facts = facts.assume_condition(
        ConditionTerm::pointer_equal(owner.clone(), displaced.clone()),
        true,
    );
    assert!(facts.equality_graph.are_equal(&owner, &displaced));
    assert!(
        resources
            .concrete_read_entries(&displaced, 4, &facts)
            .is_none()
    );
}

#[test]
fn scratch_queries_do_not_force_input_registration_at_the_next_boundary() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(856_000 + id)),
        };
        let facts = PureFactContext::new();
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
        }
        resources.synchronize_memory_equalities(&facts);
        let scratch = facts.clone();
        assert!(
            resources
                .concrete_read_entries(&at(size), 4, &scratch)
                .is_none()
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.synchronize_memory_equalities(&facts)
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "scratch query discarded the input checkpoint: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "scratch query reattached unrelated input: {samples:?}"
    );
}

#[test]
fn offset_equalities_update_already_indexed_cells() {
    let at = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(variable)),
    };
    let (owner, alias) = (at(852_000), at(852_001));
    let empty = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset.clone(), alias.offset.clone()),
        true,
    );
    assert!(facts.equality_graph.are_equal(&owner, &alias));
    assert!(
        resources.concrete_read_entries(&alias, 4, &facts).is_some(),
        "a graph equality must reach the cell index"
    );
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 4, &empty));
}

#[test]
fn whole_cell_hits_remain_indexed_beside_other_read_shapes() {
    let at = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(857_000 + id)),
    };
    let owner = at(0);
    let alias = at(1);
    let resources = ResourceContext::new()
        .unchecked_with_fact(view(&owner, 0, 4))
        .unchecked_with_fact(view(&at(2), 0, 8))
        .unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_with_element_width(
                at(3),
                0u32.into(),
                Bitvector32Term::Variable(Variable(857_100)),
                1,
            ),
        ));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset, alias.offset.clone()),
        true,
    );
    let candidates = resources
        .concrete_read_entries(&alias, 4, &facts)
        .expect("unrelated read shapes must not disable a known cell match");
    assert!(candidates.exact());
    assert_eq!(candidates.count(), 1);
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 8, &facts));
}

#[test]
fn cell_footprints_follow_merges_removals_and_normalization() {
    let at = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(858_000 + id)),
    };
    let (owner, alias) = (at(0), at(1));
    let (short, long) = (view(&owner, 0, 4), view(&alias, 0, 8));
    let zero = CResourceFact::Own(
        CResource::Memory(CMemoryRange::new_with_element_width(
            owner.clone(),
            0u32.into(),
            12u32.into(),
            1,
        )),
        Box::new(Bitvector32Term::Constant(0)),
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(short.clone())
        .unchecked_with_fact(long.clone())
        .unchecked_with_fact(zero);
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let sibling = resources.clone();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset.clone(), alias.offset.clone()),
        true,
    );
    resources.synchronize_memory_equalities(&facts);
    for bytes in [4, 8] {
        let candidates = resources
            .concrete_read_entries(&alias, bytes, &facts)
            .unwrap();
        assert!(candidates.exact());
        assert_eq!(candidates.count(), 1);
        assert!(resources.permits_memory_read(&owner, bytes, &facts));
    }
    assert!(!sibling.permits_memory_read(&owner, 8, &empty));
    assert!(!resources.permits_memory_read(&owner, 12, &facts));
    let removed = resources
        .clone()
        .without_exact_representation(&short)
        .unwrap();
    // A partial read of the longer range is still allowed by the existing
    // range checker; removing its whole-cell counterpart must prune size 4.
    assert!(removed.concrete_read_entries(&alias, 4, &facts).is_none());
    assert!(removed.permits_memory_read(&alias, 4, &facts));
    assert!(
        removed
            .concrete_read_entries(&alias, 8, &facts)
            .unwrap()
            .exact()
    );
    let empty_cells = removed.without_exact_representation(&long).unwrap();
    assert!(!empty_cells.permits_memory_read(&alias, 4, &facts));
    let restored = empty_cells.unchecked_with_fact(short).normalized(&facts);
    assert!(
        restored
            .concrete_read_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert!(restored.permits_memory_read(&alias, 4, &facts));
    assert!(!restored.permits_memory_read(&alias, 8, &facts));
}

#[test]
fn cell_footprint_merges_and_queries_do_not_scan_other_sizes() {
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(859_000 + id)),
        };
        let (owner, alias) = (at(0), at(1));
        let mut resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&alias, 0, 8 + i * 4));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let facts = empty.assume_condition(
                    ConditionTerm::pointer_offset_equal(owner.offset, alias.offset.clone()),
                    true,
                );
                resources.synchronize_memory_equalities(&facts);
                let candidates = resources.concrete_read_entries(&alias, 4, &facts).unwrap();
                assert!(candidates.exact());
                assert_eq!(candidates.count(), 1);
                assert!(resources.permits_memory_read(&alias, 4, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "merge/query scanned other footprints: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "merge/query rebuilt the larger footprint payload: {samples:?}"
    );
}

#[test]
fn logical_pointer_reads_reach_resource_index_without_equality_warmup() {
    let _session = crate::kernel::VerificationSession::enter();
    let logical_pointer_read = |memory: &CMemory, address: &Pointer, context: &PureFactContext| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new(),
            Vec::new(),
            context,
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read")
        };
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer read")
        };
        value.pointer().clone()
    };
    let memory = CMemory::new();
    let a = Pointer::symbolic(Variable(92_250));
    let b = Pointer::symbolic(Variable(92_251));
    let before = PureFactContext::new();
    let x = logical_pointer_read(&memory, &a, &before);
    let y = logical_pointer_read(&memory, &b, &before);
    let owner = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
        CMemoryRange::new_with_element_width(x, 0u32.into(), 4u32.into(), 1),
    ));
    owner.synchronize_memory_equalities(&before);
    let sibling = before.clone();
    let branch = before
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    // Ask the resource index first, without warming pointer equality or
    // invoking a spelling fallback. Producer definitions are term metadata.
    assert!(
        owner
            .concrete_read_entries(&y, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    assert!(
        owner
            .concrete_write_entries(&y, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    assert!(owner.permits_memory_read(&y, 4, &branch));
    assert!(owner.memory_write_range(&y, 4, &branch).is_some());
    assert!(!owner.permits_memory_read(&y, 4, &sibling));
    assert!(!owner.permits_memory_read(&y.offset_by_bytes(4), 4, &branch));
    assert!(owner.memory_write_range(&y, 5, &branch).is_none());
    let later = memory.store(a, CValue::typed_pointer(b, CType::Int64Pointer));
    let z = logical_pointer_read(&later, &Pointer::symbolic(Variable(92_251)), &branch);
    assert!(!owner.permits_memory_read(&z, 4, &branch));
}
