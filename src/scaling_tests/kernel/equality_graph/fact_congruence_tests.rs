// Scaling tests of `src/kernel/equality_graph/fact_congruence_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn fact_lookup_does_not_scan_unrelated_facts() {
    let mut costs = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context
                .assume_proposition(eq(call("f", vec![scalar(var(100 + i))]), var(10000 + i)));
        }
        context = context.assume_proposition(eq(var(100), var(50000)));
        let required = eq(call("f", vec![scalar(var(50000))]), var(10000));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(context.contains_known(&required));
            })
        });
        costs.push((work, map_work));
    }
    eprintln!("fact lookup costs: {costs:?}");
    // Fourfold ambient growth adds only index height, not a fact scan.
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn nested_application_registration_and_late_merge_scale_with_expression_size() {
    let mut costs = Vec::new();
    for size in [8usize, 32, 128, 512] {
        let nested = |mut value| {
            for _ in 0..size {
                value = call("nested", vec![scalar(value)]);
            }
            value
        };
        let a = nested(var(81));
        let b = nested(var(82));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_int32_equal(&a, &b));
                graph.add_int32_equality(&var(81), &var(82));
                assert!(graph.are_int32_equal(&a, &b));
            })
        });
        costs.push((size, work, map_work));
    }
    for sample in &costs[1..] {
        let base = costs[0];
        assert!(sample.1 <= base.1 * (sample.0 / base.0) * 2, "{costs:?}");
        assert!(
            sample.2
                <= base.2 * (sample.0 / base.0) * (sample.0.ilog2() as usize + 1)
                    / (base.0.ilog2() as usize + 1)
                    * 2,
            "{costs:?}"
        );
    }
}

#[test]
fn signed_addition_definedness_lookup_scales_with_alias_delta() {
    let mut costs = Vec::new();
    for size in [32u64, 64, 128] {
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut facts = PureFactContext::new().assume_condition(
                ConditionTerm::signed_add_overflows(var(61000), var(61001)),
                false,
            );
            for index in 0..size {
                facts = facts
                    .assume_proposition(eq(var(61000), var(62000 + index)))
                    .assume_condition(
                        ConditionTerm::signed_add_overflows(var(63000 + index), var(64000 + index)),
                        true,
                    );
                assert_eq!(
                    facts.decide(&ConditionTerm::signed_add_overflows(
                        var(62000 + index),
                        var(61001)
                    )),
                    Some(false)
                );
            }
        });
        costs.push(work);
    }
    assert!(costs[2] < 6 * costs[0], "{costs:?}");
}

#[test]
fn pointer_disequality_projection_ignores_unrelated_pointer_predicates() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(74000 + i)),
                    Pointer::symbolic(Variable(75000 + i)),
                ),
                false,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let source = Pointer::symbolic(Variable(72999));
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        source.clone(),
                        coordinate_pointer("storage".into(), 73000),
                    ),
                    false,
                );
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        source,
                        coordinate_pointer("storage".into(), 73001),
                    ),
                    true,
                );
                assert!(facts.contains_known(&Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(
                        PointerOffsetTerm::Variable(Variable(73000)),
                        PointerOffsetTerm::Variable(Variable(73001))
                    ),
                    false
                )));
            })
        });
        costs.push((work, map_work));
    }
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}

#[test]
fn pointer_comparison_evidence_work_ignores_unrelated_facts() {
    let mut costs = Vec::new();
    for size in [16, 64, 256] {
        let mut facts = PureFactContext::new();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    coordinate_pointer(PointerBlock::ExternalArgument, 79000 + i * 2),
                    coordinate_pointer(PointerBlock::ExternalArgument, 79001 + i * 2),
                ),
                false,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let left = coordinate_pointer(PointerBlock::ExternalArgument, 78001);
                let right = coordinate_pointer(PointerBlock::ExternalArgument, 78002);
                let alias = Pointer::symbolic(Variable(78003));
                // Registering the query before the premise must not choose a
                // canonical base that later loses the admitted comparison.
                let goal = Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(left.clone(), alias.clone()),
                    false,
                );
                assert!(!facts.contains_known(&goal));
                facts = facts
                    .assume_condition(ConditionTerm::pointer_equal(left, right.clone()), false)
                    .assume_condition(ConditionTerm::pointer_equal(right, alias), true);
                assert!(facts.contains_known(&goal));
            })
        });
        costs.push((work, map_work));
    }
    for pair in costs.windows(2) {
        assert!(pair[1].0 <= pair[0].0 * 2, "{costs:?}");
        assert!(pair[1].1 <= pair[0].1 * 2, "{costs:?}");
    }
}
