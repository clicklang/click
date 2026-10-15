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
fn checked_context_construction_attaches_address_candidates() {
    let at = |id: u64| Pointer::symbolic(Variable(860_000 + id));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(at(0), at(1)), true)
        .assume_condition(ConditionTerm::pointer_equal(at(1), at(2)), true);
    let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        at(0),
        0u32.into(),
        4u32.into(),
        1,
    ));
    for mode in 0..5 {
        let resources = match mode {
            0 => ResourceContext::new().try_compose_with_fact(owner.clone(), &facts),
            1 => ResourceContext::new()
                .try_compose_with_facts_delaying_normalization([owner.clone()], &facts),
            2 => ResourceContext::new()
                .try_compose_into_valid_context_delaying_normalization([owner.clone()], &facts),
            3 => ResourceContext::new()
                .try_compose_certified_group_into_valid_context_delaying_normalization(
                    [owner.clone()],
                    &facts,
                ),
            _ => Ok(ResourceContext::new()
                .unchecked_with_fact(owner.clone())
                .normalized(&facts)),
        }
        .unwrap();
        assert!(
            resources
                .concrete_read_entries(&at(2), 4, &facts)
                .is_some_and(|entries| entries.exact()),
            "unattached checked context: mode={mode}"
        );
        assert!(
            resources
                .concrete_write_entries(&at(2), 4, &facts)
                .is_some_and(|entries| entries.exact())
        );
        assert!(resources.permits_memory_read(&at(2), 4, &facts));
        assert!(resources.memory_write_range(&at(2), 4, &facts).is_some());
        assert!(!resources.permits_memory_read(&at(2), 4, &empty));
        assert!(!resources.permits_memory_read(&at(2), 8, &facts));
    }
}

#[test]
fn publication_in_one_branch_keeps_sibling_input_pairing() {
    for scaled in [false, true] {
        let scalar = |id: u64| Bitvector32Term::Variable(Variable(859_100 + id));
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: if scaled {
                PointerOffsetTerm::scale_int32(scalar(id), 4)
            } else {
                PointerOffsetTerm::Variable(Variable(859_100 + id))
            },
        };
        let equality = |left: u64, right: u64| {
            if scaled {
                ConditionTerm::equal(scalar(left), scalar(right))
            } else {
                ConditionTerm::pointer_offset_equal(at(left).offset, at(right).offset)
            }
        };
        let parent = PureFactContext::new();
        let first = parent.clone().assume_condition(equality(0, 1), true);
        let sibling = parent.clone().assume_condition(equality(0, 2), true);
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(at(0), 0u32.into(), 4u32.into(), 1),
        ));
        resources.synchronize_memory_equalities(&first);
        for (facts, alias) in [
            (&sibling, at(2)),
            (&first, at(1)),
            (&parent, at(0)),
            (&sibling, at(2)),
        ] {
            assert!(
                resources
                    .concrete_read_entries(&alias, 4, facts)
                    .is_some_and(|entries| entries.exact())
            );
            assert!(
                resources
                    .concrete_write_entries(&alias, 4, facts)
                    .is_some_and(|entries| entries.exact())
            );
            let cell = CMemoryRange::new_with_element_width(alias, 0u32.into(), 4u32.into(), 1);
            assert_eq!(
                resources
                    .memory_fact_candidates(&cell, true, facts)
                    .entries
                    .len(),
                1
            );
        }
        assert!(!resources.permits_memory_read(&at(1), 4, &sibling));
        assert!(!resources.permits_memory_read(&at(2), 4, &first));
        assert!(!resources.permits_memory_read(&at(1), 4, &parent));
    }
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
            Vec::new().into(),
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
    // The pure branch and resource sibling both fork before publication.
    let sibling = resources.clone();
    let connected = facts
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    resources.synchronize_memory_equalities(&facts);
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
    // Shifted whole cells register only their retained read-atom dependency.
    // Storage-relative names with symbolic coordinates are still outside the
    // concrete interval fragment, but exact address evidence does apply.
    let shifted = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            x.offset_by_bytes(8),
            0u32.into(),
            4u32.into(),
            1,
        )),
    );
    for value in [&y, &old] {
        let query = value.offset_by_bytes(8);
        let mut candidates = shifted
            .concrete_read_entries(&query, 4, &connected)
            .unwrap();
        assert!(candidates.exact());
        let entry = candidates.next().unwrap();
        assert_eq!(candidates.address(entry), Some(x.offset_by_bytes(8)));
        assert!(candidates.next().is_none());
        assert!(shifted.permits_memory_read(&query, 4, &connected));
        assert!(shifted.memory_write_range(&query, 4, &connected).is_some());
    }
    assert!(!shifted.permits_memory_read(&y.offset_by_bytes(8), 4, &facts));
    assert!(shifted.permits_memory_read(&old.offset_by_bytes(8), 4, &facts));
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
    let entries = resources
        .memory_fact_candidates(cell(alias.clone()).memory_range().unwrap(), true, &facts)
        .entries;
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
    let view_only =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(view(&owner, 0, 4));
    assert!(view_only.permits_memory_read(&alias, 4, &facts));
    assert!(view_only.memory_write_range(&alias, 4, &facts).is_none());
    assert!(
        view_only
            .without_fact_incrementally(&cell(alias), &facts)
            .is_none()
    );
}

#[test]
fn exact_address_classes_survive_unspellable_affine_shifts() {
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
    let mut candidates = resources
        .concrete_read_entries(&displaced, 4, &facts)
        .expect("exact address equality does not require spelling an affine displacement");
    let entry = candidates.next().expect("retained supplier");
    assert_eq!(candidates.address(entry), Some(owner.clone()));
    assert!(resources.permits_memory_read(&displaced, 4, &facts));
    // A nearby address has no exact class witness; an unspellable coordinate
    // cannot turn the interval classifier's unknown into a decisive miss.
    assert!(
        resources
            .concrete_read_entries(&displaced.offset_by_bytes(8), 4, &facts)
            .is_none()
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
    // Removing the whole-cell counterpart prunes its size-4 payload. The
    // remaining longer view supplies an indexed partial-read candidate.
    let partial = removed.concrete_read_entries(&alias, 4, &facts).unwrap();
    assert!(!partial.exact());
    assert_eq!(partial.count(), 1);
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
fn logical_pointer_reads_reach_resource_index_without_equality_warmup() {
    let _session = crate::kernel::VerificationSession::enter();
    let logical_pointer_read = |memory: &CMemory, address: &Pointer, context: &PureFactContext| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new().into(),
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

#[test]
fn interval_candidates_ignore_unrelated_scalar_equalities() {
    let base = Pointer::symbolic(Variable(895_000));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(895_001)),
            Bitvector32Term::Variable(Variable(895_002)),
        ),
        true,
    );
    let resources =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view(&base, 0, 32));
    let query = base.offset_by_bytes(8);
    let mut candidates = resources
        .concrete_read_entries(&query, 4, &facts)
        .expect("unrelated scalar aliases must not disable a complete interval fragment");
    assert!(!candidates.exact());
    assert!(candidates.next().is_some());
    assert!(candidates.next().is_none());
    assert!(resources.permits_memory_read(&query, 4, &facts));
}

#[test]
fn interval_candidates_follow_loaded_pointer_origins_without_spelling_retry() {
    let a = Pointer::symbolic(Variable(895_010));
    let b = Pointer::symbolic(Variable(895_011));
    let snapshot = crate::kernel::intern_c_memory(CMemory::new());
    let x = Pointer::loaded_value(&snapshot, &a);
    let y = Pointer::loaded_value(&snapshot, &b);
    let initial = PureFactContext::new();
    let connected = initial
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a, b), true);
    let resources = ResourceContext::new_with_equalities(&initial).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            x.clone(),
            0u32.into(),
            32u32.into(),
            1,
        )),
    );
    let query = y.offset_by_bytes(8);
    let mut candidates = resources
        .concrete_read_entries(&query, 4, &connected)
        .expect("retained loaded-pointer origins must use the complete interval fragment");
    assert!(!candidates.exact());
    assert!(candidates.next().is_some());
    assert!(candidates.next().is_none());
    assert!(resources.permits_memory_read(&query, 4, &connected));
    assert!(!resources.permits_memory_read(&query, 4, &initial));
    assert!(
        resources
            .memory_write_range(&query, 4, &connected)
            .is_some()
    );
    assert!(resources.memory_write_range(&query, 4, &initial).is_none());
    for start in [0u32, 8] {
        let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            if start == 0 { query.clone() } else { y.clone() },
            start.into(),
            (start + 4).into(),
            1,
        ));
        assert!(
            resources
                .directly_supporting_owned_entry(&required, &connected)
                .is_some(),
            "ownership support must use the candidate's retained graph alignment"
        );
        assert!(
            resources
                .directly_supporting_owned_entry(&required, &initial)
                .is_none()
        );
    }
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(30), 4, &connected));
    assert!(
        resources
            .memory_write_range(&y.offset_by_bytes(30), 4, &connected)
            .is_none()
    );
    let later = crate::kernel::intern_c_memory(CMemory::new().with_block("later", 8));
    let other_snapshot = Pointer::loaded_value(&later, &Pointer::symbolic(Variable(895_010)));
    assert!(!resources.permits_memory_read(&other_snapshot.offset_by_bytes(8), 4, &connected));
}

#[test]
fn interval_completeness_is_local_and_follows_late_offset_dependencies() {
    let base = Pointer::symbolic(Variable(895_020));
    let other = Pointer::symbolic(Variable(895_021));
    let offset = PointerOffsetTerm::Variable(Variable(895_022));
    let initial = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&initial)
        .unchecked_with_fact(view(&base, 0, 32))
        .unchecked_with_fact(view(&other, 0, 32));
    // Register an offset dependency before its later merge. It must taint
    // only this block, including existing interval payloads in the fork.
    let _ = resources.concrete_read_entries(
        &Pointer {
            block: base.block.clone(),
            offset: offset.clone(),
        },
        4,
        &initial,
    );
    let connected = initial.clone().assume_condition(
        ConditionTerm::pointer_equal(
            Pointer {
                block: base.block.clone(),
                offset,
            },
            base.offset_by_bytes(8),
        ),
        true,
    );
    assert_eq!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(12), 4, &connected)
            .expect("retained interval hit survives incomplete coverage")
            .count(),
        1
    );
    assert!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(48), 4, &connected)
            .is_none()
    );
    assert_eq!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(48), 4, &initial)
            .expect("complete concrete miss")
            .count(),
        0
    );
    assert!(
        resources
            .concrete_read_entries(&other.offset_by_bytes(12), 4, &connected)
            .is_some()
    );
    assert!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(12), 4, &initial)
            .is_some()
    );
    // Unknown interval completeness does not erase checked exact evidence.
    let exact = resources.clone().unchecked_with_fact(view(&base, 40, 44));
    assert!(
        exact
            .concrete_read_entries(&base.offset_by_bytes(40), 4, &connected)
            .is_some_and(|entries| entries.exact())
    );
}

#[test]
fn interval_alignment_retains_query_and_occurrence_checkpoint() {
    let base = Pointer::symbolic(Variable(895_040));
    let alias = Pointer::symbolic(Variable(895_041));
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    let cell = view(&base, 0, 4);
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(cell.clone());
    let mut candidates = resources.concrete_read_entries(&alias, 4, &facts).unwrap();
    let entry = candidates.next().unwrap();
    // Removal changes the live fork, not retained evidence or occurrence IDs.
    let removed = resources
        .clone()
        .without_exact_representation(&cell)
        .unwrap();
    assert_eq!(candidates.address(entry), Some(base.clone()));
    assert!(!removed.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 4, &empty));
    assert!(!resources.permits_memory_read(&alias, 5, &facts));
    assert!(resources.memory_write_range(&alias, 4, &facts).is_none());
}

#[test]
fn unpublished_loaded_intervals_do_not_claim_complete_supplier_coverage() {
    let a = Pointer::symbolic(Variable(895_060));
    let b = Pointer::symbolic(Variable(895_061));
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let x = Pointer::loaded_value(&memory, &a);
    let y = Pointer::loaded_value(&memory, &b);
    let facts = PureFactContext::new().assume_condition(ConditionTerm::pointer_equal(a, b), true);
    // The raw structural root has not registered x's defining load. A short
    // unrelated entry under y must not turn a missing supplier into a denial.
    let resources = ResourceContext::new()
        .unchecked_with_fact(view(&x, 0, 32))
        .unchecked_with_fact(view(&y, 0, 4));
    let query = y.offset_by_bytes(8);
    assert!(resources.concrete_read_entries(&query, 4, &facts).is_none());
    resources.synchronize_memory_equalities(&facts);
    assert!(resources.concrete_read_entries(&query, 4, &facts).is_some());
    assert!(resources.permits_memory_read(&query, 4, &facts));
}

#[test]
fn sole_symbolic_write_owner_preserves_bounds_authority_and_forks() {
    let base = Pointer::symbolic(Variable(961_100));
    let alias = Pointer::symbolic(Variable(961_101));
    let i = Bitvector32Term::Variable(Variable(961_102));
    let n = Bitvector32Term::Variable(Variable(961_103));
    let empty = PureFactContext::new();
    let bounds = empty
        .clone()
        .assume_condition(
            ConditionTerm::signed_less_equal(1u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let facts = bounds.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    let range = CMemoryRange::new_with_element_width(base.clone(), 1u32.into(), n.clone(), 1);
    let owner = CResourceFact::own_memory(range.clone());
    let resources = ResourceContext::new_with_equalities(&empty)
        .unchecked_with_fact(CResourceFact::view_memory(range.clone()))
        .unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&empty);
    let query = alias.offset_by_elements(i.clone(), 1);
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&range)
    );
    assert!(resources.memory_write_range(&query, 1, &bounds).is_none());
    assert!(resources.memory_write_range(&base, 1, &facts).is_none());
    assert!(
        resources
            .memory_write_range(&alias.offset_by_elements(n, 1), 1, &facts)
            .is_none()
    );
    assert!(resources.memory_write_range(&query, 2, &facts).is_none());
    let no_bounds = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    assert!(
        resources
            .memory_write_range(&query, 1, &no_bounds)
            .is_none()
    );
    let views = resources
        .clone()
        .without_exact_representation(&owner)
        .unwrap();
    assert!(views.memory_write_range(&query, 1, &facts).is_none());
    for quantity in [0u32, u32::MAX] {
        let invalid = views.clone().unchecked_with_fact(CResourceFact::Own(
            CResource::Memory(range.clone()),
            Box::new(quantity.into()),
        ));
        assert!(invalid.memory_write_range(&query, 1, &facts).is_none());
    }
    // Both occurrences must follow the late class merge. Selection reports
    // unknown rather than trying owners until one happens to cover the query.
    let second = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        alias,
        0u32.into(),
        range.end().clone(),
        1,
    ));
    let ambiguous = resources.clone().unchecked_with_fact(second.clone());
    assert!(ambiguous.write_access_entries(&query, 1, &facts).is_none());
    let restored = ambiguous.without_exact_representation(&second).unwrap();
    assert_eq!(restored.memory_write_range(&query, 1, &facts), Some(&range));
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&range)
    );
}

#[test]
fn memory_support_returns_retained_occurrences_through_transitive_aliases() {
    let p = Pointer::symbolic(Variable(974_000));
    let q = Pointer::symbolic(Variable(974_001));
    let r = Pointer::symbolic(Variable(974_002));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true)
        .assume_condition(ConditionTerm::pointer_equal(q, r.clone()), true);
    let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        p,
        0u32.into(),
        8u32.into(),
        1,
    ));
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(owner.clone());
    let required = view(&r, 2, 4);
    assert_eq!(
        resources.directly_supporting_fact(&required, &facts),
        Some(&owner)
    );
    let support = resources
        .directly_supporting_owned_entry(&required, &facts)
        .unwrap();
    assert_eq!(support.0, resources.occurrences_for_fact(&owner)[0]);
    assert_eq!(support.1, &owner);
    assert!(
        resources
            .directly_supporting_fact(&required, &empty)
            .is_none()
    );
}

#[test]
fn indexed_memory_support_never_promotes_zero_quantity() {
    let p = Pointer::symbolic(Variable(976_000));
    let facts = PureFactContext::new();
    let range = CMemoryRange::new_with_element_width(p, 0u32.into(), 4u32.into(), 1);
    let owner = CResourceFact::own_memory(range.clone());
    let zero = CResourceFact::Own(CResource::Memory(range), Box::new(0u32.into()));
    let resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(zero);
    assert!(!resources.satisfies_fact(&owner, &facts));
    assert!(resources.directly_supporting_fact(&owner, &facts).is_none());
    assert!(
        resources
            .directly_supporting_owned_entry(&owner, &facts)
            .is_none()
    );
    assert!(
        resources
            .without_fact_incrementally(&owner, &facts)
            .is_none()
    );
}

#[test]
fn fragment_coordinate_residues_do_not_establish_wide_pointer_adjacency() {
    let p = Pointer::symbolic(Variable(979_000));
    let positive = Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::Constant(i64::from(i32::MAX)),
    };
    let negative = Pointer {
        block: p.block,
        offset: PointerOffsetTerm::Constant(i64::from(i32::MIN)),
    };
    let own = |base, end| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            end,
            1,
        ))
    };
    let facts = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_fact(own(positive.clone(), 1u32.into()))
        .unchecked_with_fact(own(negative, 1u32.into()));
    let required = own(positive, 2u32.into());
    // The first piece's end has INT32_MIN's residue, but its true byte
    // address is 2^31. The negative piece cannot fill the adjacent byte.
    assert!(!resources.satisfies_fact(&required, &facts));
    assert!(
        resources
            .without_fact_incrementally(&required, &facts)
            .is_none()
    );
}

#[test]
fn storage_ownership_follows_transitive_address_equality() {
    let base = Pointer::symbolic(Variable(894_000));
    let alias = Pointer::symbolic(Variable(894_001));
    let last = Pointer::symbolic(Variable(894_002));
    let empty = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            0u32.into(),
            48u32.into(),
            1,
        )),
    );
    let facts = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(alias, last.clone()), true);
    assert!(resources.owns_storage_access(&last.offset_by_bytes(8), 40, &facts));
    assert!(!resources.owns_storage_access(&last.offset_by_bytes(9), 40, &facts));
    assert!(!resources.owns_storage_access(&last, 40, &empty));
    assert!(
        !ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(view(&base, 0, 48))
            .owns_storage_access(&last, 40, &facts)
    );
}

#[test]
fn object_evidence_uses_provenance_classes_and_live_nonempty_occurrences() {
    let external = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(898_000 + id)),
    };
    let source = external(0);
    let target = external(1);
    let empty = PureFactContext::new();
    let fact = view(&source, 0, 4);
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(fact.clone());
    let address_only = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(source.clone(), target.clone()),
        true,
    );
    assert!(
        resources
            .memory_object_evidence(&target, &address_only)
            .is_none()
    );
    let shared_object = address_only.assume_condition(
        ConditionTerm::pointer_equal(source.object_identity(), target.object_identity()),
        true,
    );
    assert_eq!(
        resources.memory_object_evidence(&target, &shared_object),
        Some(&fact)
    );
    assert!(resources.memory_object_evidence(&target, &empty).is_none());
    assert_eq!(
        resources.memory_object_evidence(&source.offset_by_bytes(100), &empty),
        Some(&fact)
    );
    assert!(!resources.owns_storage_access(&source, 4, &empty));
    let owner = CResourceFact::own_memory(fact.memory_range().unwrap().clone());
    let owned = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(owner.clone());
    let gone = owned
        .clone()
        .without_fact_incrementally(&owner, &empty)
        .unwrap();
    assert!(gone.memory_object_evidence(&source, &empty).is_none());
    assert_eq!(owned.memory_object_evidence(&source, &empty), Some(&owner));
    for fact in [
        view(&source, 0, 0),
        CResourceFact::own_quantity(
            CResource::Memory(CMemoryRange::new_with_element_width(
                source.clone(),
                0u32.into(),
                4u32.into(),
                1,
            )),
            0u32.into(),
        ),
    ] {
        assert!(
            ResourceContext::new_with_equalities(&empty)
                .unchecked_with_fact(fact)
                .memory_object_evidence(&source, &empty)
                .is_none()
        );
    }
}

// A read congruence learned through whole offsets must reach ownership's
// incremental class index, not just return true from an equality query.
#[test]
fn typed_read_congruence_publishes_late_ownership_class_updates() {
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let p = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(998_001)),
    };
    let q = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(998_002)),
    };
    let x = Pointer::loaded_value(&memory, &p);
    let y = Pointer::loaded_value(&memory, &q);
    let empty = PureFactContext::new();
    let resources =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(view(&x, 0, 32));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(8), 4, &empty));
    let joined = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(p.offset, q.offset),
        true,
    );
    assert!(resources.permits_memory_read(&y.offset_by_bytes(8), 4, &joined));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(30), 4, &joined));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(8), 4, &empty));
}

#[test]
fn symbolic_owned_suffix_start_checks_bounds_and_retained_authority() {
    let base = Pointer::symbolic(Variable(989_000));
    let split = Bitvector32Term::Variable(Variable(989_001));
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::uint64_less_than(split.clone(), Bitvector32Term::UInt64Constant(32)),
        true,
    );
    let prefix = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(0),
        split.clone(),
        1,
    );
    let suffix = CMemoryRange::new_wide(
        base.clone(),
        split.clone(),
        Bitvector32Term::UInt64Constant(32),
        1,
    );
    let owner = CResourceFact::own_memory(suffix.clone());
    let resources = ResourceContext::new_with_equalities(&empty)
        .unchecked_with_fact(CResourceFact::own_memory(prefix))
        .unchecked_with_fact(CResourceFact::view_memory(suffix.clone()))
        .unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&empty);
    let query = suffix.start_pointer();
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&suffix)
    );
    assert!(resources.memory_write_range(&query, 1, &empty).is_none());
    assert!(resources.memory_write_range(&query, 2, &facts).is_none());
    assert!(
        resources
            .memory_write_range(
                &CMemoryRange::new_wide(
                    base,
                    Bitvector32Term::UInt64Constant(32),
                    Bitvector32Term::UInt64Constant(33),
                    1
                )
                .start_pointer(),
                1,
                &facts
            )
            .is_none()
    );
    let removed = resources
        .clone()
        .without_exact_representation(&owner)
        .unwrap();
    assert!(removed.memory_write_range(&query, 1, &facts).is_none());
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&suffix)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/memory_equality_index/cell_tests.rs");
}
