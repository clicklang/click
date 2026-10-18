// Scaling tests of `src/kernel/equality_graph/terms.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn addition_congruence_late_merge_work_scales_with_affected_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
            graph.add_offset_equality(&add(var(1), var(10 + i)), &var(20_000 + i));
        }
        let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_offset_equality(&var(0), &var(1));
                for i in 0..size {
                    assert!(graph.are_offsets_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 80 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 512 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn addition_congruence_forks_do_not_reindex_unrelated_parents() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
        }
        let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    // Argument order must not move the class with many
                    // parents under this newly registered singleton.
                    branch.add_offset_equality(&var(20_000 + i), &var(0));
                    assert!(branch.are_offsets_equal(&add(var(20_000 + i), var(10)), &var(10_000)));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 512 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        assert!(!graph.are_offsets_equal(&var(20_000), &var(0)));
    }
}

#[test]
fn offset_graph_construction_and_fork_queries_scale_with_indexed_work() {
    let offset = |id| PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(id))),
        byte_width: 4,
    };
    for size in [16u64, 64, 256, 1024] {
        let ((graph, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                for i in 0..size {
                    graph.add_offset_equality(&offset(i), &offset(i + 1));
                    assert!(graph.are_offsets_equal(&offset(0), &offset(i + 1)));
                }
                graph
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 40 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 160 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        let (_, fork_work) = crate::persistent::measure_persistent_work(|| {
            let mut branch = graph.clone();
            branch.add_offset_equality(&offset(size), &offset(size + 1));
            assert!(branch.are_offsets_equal(&offset(0), &offset(size + 1)));
            assert!(!graph.are_offsets_equal(&offset(0), &offset(size + 1)));
        });
        assert!(
            fork_work < 160 * logarithm,
            "size={size}, fork work={fork_work}"
        );
    }
}

#[test]
fn late_wide_zero_reindexes_only_its_existing_offsets() {
    let mut measured = Vec::new();
    for size in [4u64, 16, 64] {
        let mut graph = EqualityGraph::default();
        let scaled = |base: &Pointer, value| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Int64Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(value))),
                byte_width: 4,
                unsigned: true,
            },
        };
        for i in 0..size {
            let base = Pointer::symbolic(Variable(896_000 + i));
            assert!(!graph.are_equal(&scaled(&base, 897_000 + i), &base));
        }
        let base = Pointer::symbolic(Variable(898_000));
        let pointer = scaled(&base, 898_001);
        assert!(!graph.are_equal(&pointer, &base));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(898_001)),
                &Bitvector32Term::UInt64Constant(0),
            );
        });
        assert!(graph.are_equal(&pointer, &base));
        measured.push(work);
    }
    assert!(
        measured.iter().all(|work| *work <= measured[0] + 32),
        "unrelated wide offsets increased selected propagation: {measured:?}"
    );
}
