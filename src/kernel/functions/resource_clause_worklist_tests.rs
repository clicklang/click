use super::*;

#[test]
fn adjacent_supply_wakes_wide_memory_waiter() {
    let base = Pointer {
        block: PointerBlock::Concrete("resource-clause-adjacent".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let wide = CResourceFact::view_memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(2),
    ));
    let left = CResourceFact::view_memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let right = CResourceFact::view_memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
    ));
    let assumptions = PureFactContext::new();
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![wide.clone()], &mut dependencies, &mut waiters);
    let evaluated = vec![None];
    let mut queued = vec![false];
    let mut pending = VecDeque::new();
    let section_supply = ResourceContext::new().unchecked_with_fact(left.clone());

    assert!(!section_supply.satisfies_fact(&wide, &assumptions));
    resource_clause_enqueue_waiters(
        &left,
        &assumptions,
        &section_supply,
        &evaluated,
        &mut queued,
        &mut pending,
        &dependencies,
        &waiters,
    );
    assert!(pending.is_empty());

    let section_supply = section_supply.unchecked_with_fact(right.clone());
    assert!(section_supply.satisfies_fact(&wide, &assumptions));
    resource_clause_enqueue_waiters(
        &right,
        &assumptions,
        &section_supply,
        &evaluated,
        &mut queued,
        &mut pending,
        &dependencies,
        &waiters,
    );
    assert_eq!(pending, VecDeque::from([0]));
}

/// Same-block disjoint ranges have one real dependency edge apiece.  The
/// interval index must visit those edges, not every waiter sharing the
/// block key.  The exact candidate count is the regression: the old
/// `MemoryBlock` index would produce `size * size` visits here.
#[test]
fn same_block_disjoint_waiters_use_interval_candidates() {
    let base = Pointer {
        block: PointerBlock::Concrete("resource-clause-disjoint".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let samples = [4_usize, 8, 16, 32]
            .into_iter()
            .map(|size| {
                let mut dependencies = vec![Vec::new(); size];
                let mut waiters = ResourceClauseWaiterIndex::default();
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let dependency = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    resource_clause_register_waiters(
                        index,
                        vec![dependency],
                        &mut dependencies,
                        &mut waiters,
                    );
                }
                let mut candidate_visits = 0;
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let supplied = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    let candidates = waiters.candidates_for_supplied(&supplied);
                    candidate_visits += candidates.len();
                    assert_eq!(
                        candidates.into_iter().collect::<Vec<_>>(),
                        vec![index],
                        "a disjoint supplied range woke unrelated same-block waiters: size={size} index={index}"
                    );
                }
                (size, candidate_visits)
            })
            .collect::<Vec<_>>();
    assert_eq!(
        samples,
        vec![(4, 4), (8, 8), (16, 16), (32, 32)],
        "same-block interval candidate work should follow actual dependency edges"
    );
}

#[test]
fn comparable_constant_bases_share_interval_space() {
    let block = PointerBlock::Concrete("resource-clause-base-aware".to_string());
    let dependency_base = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let supplied_base = Pointer {
        block,
        offset: PointerOffsetTerm::Constant(8),
    };
    let dependency = CResourceFact::view_memory(CMemoryRange::new(
        dependency_base,
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(3),
    ));
    let supplied = CResourceFact::view_memory(CMemoryRange::new(
        supplied_base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn concrete_memory_waiters_share_physical_byte_space_across_widths() {
    let base = Pointer {
        block: PointerBlock::Concrete("resource-clause-byte-space".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let dependency = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(8),
        Bitvector32Term::Constant(12),
        1,
    ));
    let supplied = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        base,
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(3),
        4,
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn symbolic_memory_waiters_keep_conservative_block_fallback() {
    let base = Pointer {
        block: PointerBlock::Concrete("resource-clause-symbolic".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let dependency = CResourceFact::view_memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Variable(Variable(9_901)),
    ));
    let supplied = CResourceFact::view_memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&supplied),
        BTreeSet::from([0])
    );
}

#[test]
fn concrete_waiter_block_fallback_registers_and_unregisters_symmetrically() {
    let base = Pointer {
        block: PointerBlock::Concrete("resource-clause-fallback-lifetime".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let dependency = CResourceFact::view_memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let symbolic_supplied = CResourceFact::view_memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Variable(Variable(9_902)),
    ));
    let mut dependencies = vec![Vec::new()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
    assert_eq!(
        waiters.candidates_for_supplied(&symbolic_supplied),
        BTreeSet::from([0])
    );
    resource_clause_unregister_waiters(0, &mut dependencies, &mut waiters);
    assert!(
        waiters
            .candidates_for_supplied(&symbolic_supplied)
            .is_empty()
    );
}
