// Scaling tests of `src/kernel/equality_graph/uint64_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn integer_address_queries_ignore_unrelated_equations_and_reuse_definitions() {
    let _session = VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(i)),
                &Bitvector32Term::Variable(Variable(i + 10_000)),
            );
        }
        let bits = Bitvector32Term::Variable(Variable(960_004));
        let decoded = Pointer::integer_address(bits.clone());
        assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
        let (((), work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..16 {
                    assert!(graph.are_uint64_equal(&raw_address(&decoded), &bits));
                }
            })
        });
        samples.push((work, maps));
    }
    assert!(samples.windows(2).all(|p| p[0].0 == p[1].0 && p[1].1 <= p[0].1 * 2), "{samples:?}");
}

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
                facts = facts
                    .clone()
                    .assume_condition(ConditionTerm::uint64_equal(var(i), var(i + 1)), true);
            }
            facts = facts.clone().assume_condition(
                ConditionTerm::uint64_equal(var(size), Bitvector32Term::UInt64Constant(37)),
                true,
            );
            assert_eq!(facts.wide_constant_from_equalities(&var(0)), Some(37));
            assert!(facts.uint64_values_equal_for_range_resolution(
                &var(0),
                &Bitvector32Term::UInt64Constant(37)
            ));
        });
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}
