// Scaling tests of `src/kernel/equality_graph/int32_addition_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn int32_addition_late_merge_and_fork_work_is_indexed() {
    for size in [16u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_int32_equality(&add(var(1), var(100 + i)), &var(10_000 + i));
            graph.add_int32_equality(&add(var(2), var(100 + i)), &var(20_000 + i));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.add_int32_equality(&var(1), &var(2));
                for i in 0..size {
                    assert!(graph.are_int32_equal(&var(10_000 + i), &var(20_000 + i)));
                }
            })
        });
        assert!(work < 100 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    let mut branch = graph.clone();
                    branch.add_int32_equality(&var(30_000 + i), &var(1));
                    assert!(branch.are_int32_equal(&add(var(30_000 + i), var(100)), &var(10_000)));
                }
            })
        });
        assert!(work < 200 * size as usize, "size={size}, fork work={work}");
        assert!(
            map_work < 1000 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
fn int32_addition_nested_registration_and_literal_propagation_scale() {
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut term = var(1);
        for _ in 0..size {
            term = add(term, Bitvector32Term::Constant(1));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                graph.add_int32_equality(&term, &var(10));
                graph.add_int32_equality(&var(1), &Bitvector32Term::Constant(0));
                assert!(graph.are_int32_equal(&var(10), &Bitvector32Term::Constant(size as u32)));
            })
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
