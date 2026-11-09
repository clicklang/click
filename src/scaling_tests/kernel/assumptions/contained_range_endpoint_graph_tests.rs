// Scaling tests of `src/kernel/assumptions.rs` (module `contained_range_endpoint_graph_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn signed_containment_order_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
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
    for size in [16u64, 64, 256, 512] {
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

#[test]
fn retained_memory_bound_candidates_do_not_export_shared_endpoints() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineOperandView as V};
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let lower = endpoint(9_331_001);
        let upper = variable(9_331_002);
        let retained = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &lower)
            .unwrap();
        let source = condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            [V::Shared(&retained), V::Legacy(&upper)],
        );
        let mut context = PureFactContext::new().assume_condition(source, true);
        for n in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(variable(9_340_000 + n), MachineTerm::constant(n as u32)),
                true,
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let candidates: Vec<_> =
                recorded_less_equal_candidates(&lower, &upper, &context).collect();
            assert!(!candidates.is_empty());
            assert!(candidates.iter().any(|(l, _, _)| {
                crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
                    *l,
                    V::Legacy(&lower),
                    &context,
                )
            }));
            assert!(
                recorded_less_equal_candidates(&lower, &variable(9_331_003), &context)
                    .next()
                    .is_none()
            );
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work < 500, "size={size}, work={work}");
    }
}

#[test]
fn retained_memory_bound_sources_keep_written_direction_and_branch_isolation() {
    let _session = crate::kernel::VerificationSession::enter();
    let lower = endpoint(9_331_101);
    let upper = variable(9_331_102);
    let reversed = ConditionTerm::signed_greater_equal(upper.clone(), lower.clone());
    let source = ConditionTerm::signed_less_than(lower.clone(), upper.clone());
    let parent = PureFactContext::new().assume_condition(reversed, true);
    assert!(
        recorded_less_equal_candidates(&lower, &upper, &parent)
            .next()
            .is_none()
    );
    let branch = parent.clone().assume_condition(source.clone(), true);
    assert!(recorded_less_equal_candidates(&lower, &upper, &branch).any(|(_, _, strict)| strict));
    let withdrawn = branch.without_exact_fact(&Proposition::ConditionIs(source, true));
    assert!(
        recorded_less_equal_candidates(&lower, &upper, &withdrawn)
            .next()
            .is_none()
    );
    assert!(
        recorded_less_equal_candidates(&lower, &upper, &parent)
            .next()
            .is_none()
    );
}
