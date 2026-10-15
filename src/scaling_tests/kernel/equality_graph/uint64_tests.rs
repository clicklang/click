// Scaling tests of `src/kernel/equality_graph/uint64_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_congruence_queries_do_not_scan_unrelated_equalities() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let p = Pointer::symbolic(Variable(940_001));
        let q = Pointer::symbolic(Variable(940_002));
        let a = Bitvector32Term::Variable(Variable(940_003));
        let b = Bitvector32Term::Variable(Variable(940_004));
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(i)),
                &Bitvector32Term::Variable(Variable(i + 10_000)),
            );
        }
        graph.add_uint64_equality(&a, &packed(&b, &p));
        graph.add_equality(&p, &q);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_uint64_equal(&a, &packed(&b, &q))
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated facts changed query work at {size}"
            );
        }
        previous = Some(work);
    }
}
