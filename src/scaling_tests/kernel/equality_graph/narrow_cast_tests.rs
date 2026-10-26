// Scaling tests of `src/kernel/equality_graph/narrow_cast_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Interning a narrow cast adds its rule-K7 word from the operand's class:
/// constant work per cast, so `size` distinct casts, and a chain of `size`
/// nested casts (each operand a sum over a narrow cast), intern in work linear in
/// `size`. A word built from the operand's term would re-intern the chain
/// at every level.
#[test]
fn narrow_cast_words_intern_in_work_linear_in_the_casts() {
    for size in [16u64, 64, 256, 512] {
        let _session = VerificationSession::enter();
        let mut chain = var(174_000);
        for level in 0..size {
            let destination = if level % 2 == 0 { Ty::Int16 } else { Ty::UInt8 };
            chain = Bitvector32Term::machine_integer_cast(
                Ty::UInt32,
                destination,
                Bitvector32Term::add(chain, Bitvector32Term::Constant(1)),
            );
        }
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let graph = EqualityGraph::default();
            for i in 0..size {
                let cast =
                    Bitvector32Term::machine_integer_cast(Ty::UInt32, Ty::UInt8, var(175_000 + i));
                let mask =
                    Bitvector32Term::bitwise_and(var(175_000 + i), Bitvector32Term::Constant(255));
                assert!(graph.are_int32_equal(&cast, &mask));
            }
            assert!(!graph.are_int32_equal(&chain, &var(174_000)));
        });
        assert!(work < 400 * size as usize, "size={size}, work={work}");
    }
}
