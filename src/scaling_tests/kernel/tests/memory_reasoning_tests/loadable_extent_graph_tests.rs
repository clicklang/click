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

/// Catches a loadability or separation index that copies itself when a
/// forked context files one more fact: the block index is persistent, so
/// the fork shares every other block's facts with its parent instead of
/// copying an index that grows with the path.
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
    }
}
