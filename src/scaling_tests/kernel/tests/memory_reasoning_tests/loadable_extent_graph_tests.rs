// Scaling tests of `src/kernel/tests/memory_reasoning_tests.rs` (module `loadable_extent_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn direct_loadable_extent_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let memory = CMemory::new();
        let base = Pointer::symbolic(Variable(9_320_010));
        let range_bytes = extent(var(0));
        let fact = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: range_bytes.clone(),
            wide: false,
        };
        let mut context = PureFactContext::new().assume_proposition(fact);
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let goal_bytes = extent(var(index));
                assert!(context.proves_memory_loadable_for_memory_resolution(
                    &memory,
                    &base,
                    &goal_bytes,
                ));
                assert!(context.proves_loadable_region_from_range(
                    &base,
                    &range_bytes,
                    &base,
                    &goal_bytes,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

/// Catches a loadability, loadability-shape, or separation index that copies
/// itself or is rebuilt when a forked context files one more fact: the block
/// indexes are persistent, so the fork shares every other block's facts with
/// its parent instead of copying an index that grows with the path.
#[test]
fn filing_a_loadable_fact_in_a_fork_shares_every_other_block() {
    let memory = CMemory::new();
    let loadable = |id: u64| Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer::symbolic(Variable(9_330_000 + id)),
        bytes: extent(var(id)),
        wide: false,
    };
    let mut parent = PureFactContext::new();
    for id in 0..64 {
        parent = parent.assume_proposition(loadable(id));
    }
    let fork = parent.clone().assume_proposition(loadable(1_000));
    for id in 0..64 {
        let block = Pointer::symbolic(Variable(9_330_000 + id)).block;
        let (Some(before), Some(after)) = (
            parent.memory_loadable_facts.get(&block),
            fork.memory_loadable_facts.get(&block),
        ) else {
            panic!("block {id} keeps its loadability fact");
        };
        assert!(
            before.shares_root_with(after),
            "the fork copied the facts of an untouched block {id}"
        );
        let (Some(before), Some(after)) = (
            parent.memory_loadable_shape_facts.get(&block),
            fork.memory_loadable_shape_facts.get(&block),
        ) else {
            panic!("block {id} keeps its loadability shape");
        };
        assert!(
            before.shares_root_with(after),
            "the fork rebuilt the shape index of an untouched block {id}"
        );
    }
    let new_base = Pointer::symbolic(Variable(9_330_000 + 1_000));
    assert_eq!(
        fork.memory_loadable_exact_candidates_for_base(&new_base)
            .cloned()
            .collect::<Vec<_>>(),
        vec![loadable(1_000)]
    );
}

/// Catches a memory-load condition index that is rebuilt over every
/// condition fact after an insertion: the index is persistent and updated
/// per fact, so a fork that files one more load condition still shares
/// every other load's bucket with its parent.
#[test]
fn filing_a_load_condition_in_a_fork_shares_every_other_load() {
    let pointer = |id: u64| Pointer {
        block: format!("load-condition-index-{id}").into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let load_condition = |id: u64| {
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(CMemory::new()),
                Box::new(pointer(id)),
                crate::kernel::LoadKind::Bits32,
            ),
            var(id),
        )
    };
    let key = |id: u64| {
        let pointer = pointer(id);
        (
            pointer.block.clone(),
            crate::kernel::assumptions::memory_blind_pointer_fingerprint(&pointer),
        )
    };
    let mut parent = PureFactContext::new();
    for id in 0..64 {
        parent = parent.assume_condition(load_condition(id), true);
    }
    let fork = parent.clone().assume_condition(load_condition(1_000), true);
    for id in 0..64 {
        let (Some(before), Some(after)) = (
            parent.memory_load_condition_facts.get(&key(id)),
            fork.memory_load_condition_facts.get(&key(id)),
        ) else {
            panic!("load {id} keeps its condition");
        };
        assert!(
            before.shares_root_with(after),
            "the fork rebuilt the bucket of an untouched load {id}"
        );
    }
    let candidates = fork
        .exact_memory_load_condition_candidates(&pointer(1_000))
        .map(|(condition, value)| (condition.clone(), value))
        .collect::<Vec<_>>();
    assert_eq!(candidates, vec![(load_condition(1_000), true)]);
    let withdrawn = fork.without_exact_fact(&Proposition::ConditionIs(load_condition(1_000), true));
    assert!(
        withdrawn
            .exact_memory_load_condition_candidates(&pointer(1_000))
            .next()
            .is_none()
    );
}
