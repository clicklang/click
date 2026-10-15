// Scaling tests of `src/kernel/primitives/resource_algebra.rs` (module `zero_quantity_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn quantity_query_work_is_indexed_over_separately_retained_units() {
    let assumptions = PureFactContext::new();
    let samples = [16_u32, 64, 256, 1024].map(|size| {
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|_| required(Bitvector32Term::Constant(1))));
        let ((), work) = crate::persistent::measure_persistent_work(|| {
            assert!(
                context.satisfies_fact(&required(Bitvector32Term::Constant(size)), &assumptions)
            );
            assert!(
                !context
                    .satisfies_fact(&required(Bitvector32Term::Constant(size + 1)), &assumptions)
            );
        });
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 16 * index, "{samples:?}");
    }
}

#[test]
fn zero_ownership_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        context = context.assume_condition(
            ConditionTerm::equal(var(size), Bitvector32Term::Constant(0)),
            true,
        );
        let empty = ResourceContext::new();
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                assert!(empty.satisfies_fact(&required(var(index)), &context));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}
