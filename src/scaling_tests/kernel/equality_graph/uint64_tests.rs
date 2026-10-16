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

#[test]
fn range_values_and_constants_resolve_long_wide_equality_chains() {
    use crate::kernel::{ConditionTerm, PureFactContext};
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let var = |i| Bitvector32Term::Variable(Variable(950_000 + i));
        let mut facts = PureFactContext::new();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                facts = facts.clone().assume_condition(ConditionTerm::uint64_equal(var(i), var(i + 1)), true);
            }
            facts = facts.clone().assume_condition(ConditionTerm::uint64_equal(var(size), Bitvector32Term::UInt64Constant(37)), true);
            assert_eq!(facts.wide_constant_from_equalities(&var(0)), Some(37));
            assert!(facts.uint64_values_equal_for_range_resolution(&var(0), &Bitvector32Term::UInt64Constant(37)));
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}
