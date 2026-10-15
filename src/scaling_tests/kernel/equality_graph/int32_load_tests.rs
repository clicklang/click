// Scaling tests of `src/kernel/equality_graph/int32_load_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn int32_load_late_merge_and_fork_work_scales_with_affected_applications() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let indexed = |index, suffix| Pointer {
            block: "array".into(),
            offset: PointerOffsetTerm::Add(
                Box::new(address(index).offset),
                Box::new(PointerOffsetTerm::Variable(Variable(100 + suffix))),
            ),
        };
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_int32_equality(&load(&memory, &indexed(1, i), 4), &var(10_000 + i));
            graph.add_int32_equality(&load(&memory, &indexed(2, i), 4), &var(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&var(1), &var(2));
                for i in 0..size {
                    assert!(graph.are_int32_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&var(30_000 + i), &var(1));
                    let fresh = load(&memory, &indexed(30_000 + i, 0), 4);
                    assert!(branch.are_int32_equal(&fresh, &var(10_000)));
                }
            })
        });
        assert!(work < 250 * size as usize, "size={size}, fork work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn int32_load_nested_registration_and_late_closure_are_iterative_and_scale() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let nested = |mut value| {
            for _ in 0..size {
                value = load(
                    &memory,
                    &Pointer {
                        block: "array".into(),
                        offset: PointerOffsetTerm::scale_int32(value, 4),
                    },
                    4,
                );
            }
            value
        };
        let left = nested(var(1));
        let right = nested(var(2));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                assert!(!graph.are_int32_equal(&left, &right));
                graph.add_int32_equality(&var(1), &var(2));
                assert!(graph.are_int32_equal(&left, &right));
            })
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 2000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
