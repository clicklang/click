// Scaling tests of `src/kernel/api/contract_certification/contract_claims.rs` (module `range_list_equality_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn certified_range_list_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(9200));
        let range = |value| {
            CMemoryRange::new(
                base.clone(),
                Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
                Bitvector32Term::Constant(16),
            )
        };
        let left = range(var(0));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let right = range(var(index));
                assert!(memory_range_lists_definitionally_equal(
                    std::slice::from_ref(&left),
                    std::slice::from_ref(&right),
                    &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}
