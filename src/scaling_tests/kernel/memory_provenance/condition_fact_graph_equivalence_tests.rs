// Scaling tests of `src/kernel/memory_provenance.rs` (module `condition_fact_graph_equivalence_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn condition_fact_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let source = less_than(sum(var(0)), var(9000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let target = less_than(sum(var(index)), var(9000));
                assert!(c_condition_facts_equivalent_for_memory_resolution(
                    &source, &target, &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}
