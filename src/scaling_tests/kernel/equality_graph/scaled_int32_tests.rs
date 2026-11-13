// Scaling tests of `src/kernel/equality_graph/scaled_int32_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn scaled_int32_late_merges_and_constant_evaluation_scale_with_affected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 1..=size {
            graph.add_offset_equality(&scaled(1, i as i64), &offset(10_000 + i));
            graph.add_offset_equality(&scaled(2, i as i64), &offset(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&scalar(1), &scalar(2));
                // The heavy class acquires a literal from a singleton.
                graph.add_int32_equality(&MachineTerm::constant(3), &scalar(1));
                for i in 1..=size {
                    assert!(graph.are_offsets_equal(&offset(10_000 + i), &offset(20_000 + i)));
                    assert!(graph.are_offsets_equal(
                        &offset(10_000 + i),
                        &PointerOffsetTerm::Constant(3 * i as i64)
                    ));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn scaled_int32_forks_do_not_reindex_unaffected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 1..=size {
            graph.add_offset_equality(&scaled(1, i as i64), &offset(10_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&scalar(20_000 + i), &scalar(1));
                    assert!(branch.are_offsets_equal(&scaled(20_000 + i, 1), &offset(10_001)));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 600 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        assert!(!graph.are_int32_equal(&scalar(20_000), &scalar(1)));
    }
}

#[test]
fn learning_a_literal_does_not_revisit_unrelated_boolean_parents() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for value in 0..size {
            graph.add_condition(
                &ConditionTerm::equal(scalar(1), MachineTerm::constant(value as u32)),
                false,
            );
        }
        graph.add_offset_equality(&scaled(1, 4), &offset(10));
        let sibling = graph.clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_int32_equality(&scalar(1), &MachineTerm::constant(2048));
            assert!(graph.are_offsets_equal(&offset(10), &PointerOffsetTerm::Constant(8192)));
        });
        assert!(!sibling.are_offsets_equal(&offset(10), &PointerOffsetTerm::Constant(8192)));
        assert!(graph.knows_condition(
            &ConditionTerm::equal(scalar(1), MachineTerm::constant(0)),
            false
        ));
        samples.push((size, work));
    }
    let (smallest, base) = samples[0];
    for (size, work) in &samples {
        assert!(
            *work <= base + 8 * (size / smallest).ilog2() as usize,
            "literal learning: {samples:?}"
        );
    }
}

/// Admitting a byte product's no-overflow fact is one keyed lookup of its
/// byte-offset node and one merge: constant work as unrelated products, their
/// facts, and unrelated offset aliases grow, and work bounded by the affected
/// parents as aliases of the byte offset itself grow.
#[test]
fn a_byte_product_merge_is_keyed_and_ignores_unrelated_products() {
    let mut unrelated_samples = Vec::new();
    let mut related_samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            let id = 1_000 + i;
            graph.add_condition(&no_overflow(id, 4, true), false);
            graph.add_offset_equality(&byte_product(id, 8, true), &offset(10_000 + i));
            graph.add_offset_equality(&scaled(id, 4), &offset(20_000 + i));
        }
        graph.add_offset_equality(&nested(byte_product(1, 4, true)), &offset(10));
        graph.add_offset_equality(&nested(scaled(1, 4)), &offset(11));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_condition(&no_overflow(1, 4, true), false);
            assert!(graph.are_offsets_equal(&offset(10), &offset(11)));
        });
        unrelated_samples.push(work);

        let mut related = EqualityGraph::default();
        for i in 0..size {
            related.add_offset_equality(
                &PointerOffsetTerm::Add(
                    Box::new(byte_product(1, 4, true)),
                    Box::new(offset(30_000 + i)),
                ),
                &offset(40_000 + i),
            );
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            related.add_condition(&no_overflow(1, 4, true), false);
            assert!(related.are_offsets_equal(&byte_product(1, 4, true), &scaled(1, 4)));
        });
        assert!(
            work < 100 * size as usize,
            "size={size}, related work={work}"
        );
        related_samples.push(work);
    }
    assert!(
        unrelated_samples
            .iter()
            .all(|work| *work == unrelated_samples[0]),
        "unrelated products changed the merge's work: {unrelated_samples:?}"
    );
    assert!(
        related_samples
            .windows(2)
            .all(|pair| pair[1] <= pair[0] * 8),
        "related work grew faster than its affected parents: {related_samples:?}"
    );
}
