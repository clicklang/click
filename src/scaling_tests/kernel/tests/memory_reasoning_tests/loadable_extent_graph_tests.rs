// Scaling tests of `src/kernel/tests/memory_reasoning_tests.rs` (module `loadable_extent_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn direct_loadable_extent_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
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
