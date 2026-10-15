// Scaling tests of `src/kernel/assumptions.rs` (module `contained_range_endpoint_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn signed_containment_order_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(exact_less_equal_for_memory_resolution(
                    &endpoint(0),
                    &endpoint(index),
                    &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn recorded_order_fact_graph_matches_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let lower = variable(9_330_010);
        let upper = variable(9_330_011);
        let mut context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(endpoint(0), upper.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(lower.clone(), endpoint(0)),
                true,
            );
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(exact_less_equal_for_memory_resolution(
                    &endpoint(index),
                    &upper,
                    &context,
                ));
                assert!(exact_less_equal_for_memory_resolution(
                    &lower,
                    &endpoint(index),
                    &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 400 * size as usize, "size={size}, work={work}");
    }
}
