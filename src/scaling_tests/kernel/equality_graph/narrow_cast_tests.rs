// Scaling tests of `src/kernel/equality_graph/narrow_cast_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Interning a narrow cast adds its rule-K7' word from the operand's class:
/// constant work per cast, so `size` distinct casts, and a chain of `size`
/// nested casts (each operand a sum over a narrow cast), intern in work linear in
/// `size`. A word built from the operand's term would re-intern the chain
/// at every level.
fn assert_narrow_cast_work(size: u64) {
    let _session = VerificationSession::enter();
    let mut chain = var(174_000);
    for level in 0..size {
        let destination = if level % 2 == 0 { Ty::Int16 } else { Ty::UInt8 };
        // Each level adds one to the previous cast's widening.
        let word = if level == 0 {
            chain
        } else {
            let previous = if level % 2 == 0 { Ty::UInt8 } else { Ty::Int16 };
            Bitvector32Term::machine_integer_cast(previous, Ty::UInt32, chain)
        };
        chain = Bitvector32Term::machine_integer_cast(
            Ty::UInt32,
            destination,
            Bitvector32Term::add(word, Bitvector32Term::Constant(1)),
        );
    }
    let graph = EqualityGraph::default();
    let ((), casts) = crate::instrumentation::measure_deterministic_work(|| {
        for i in 0..size {
            let cast =
                Bitvector32Term::machine_integer_cast(Ty::UInt32, Ty::UInt8, var(175_000 + i));
            let widened = Bitvector32Term::machine_integer_cast(Ty::UInt8, Ty::UInt32, cast);
            let mask =
                Bitvector32Term::bitwise_and(var(175_000 + i), Bitvector32Term::Constant(255));
            assert!(graph.are_int32_equal(&widened, &mask));
        }
    });
    let last = if size % 2 == 0 { Ty::UInt8 } else { Ty::Int16 };
    let ((), chain_work) = crate::instrumentation::measure_deterministic_work(|| {
        let chain = Bitvector32Term::machine_integer_cast(last, Ty::UInt32, chain.clone());
        assert!(!graph.are_int32_equal(&chain, &var(174_000)));
    });
    // The chain's `int32` widening is σ of its `uint32` one (the
    // sibling relation): σ distributes down the chain once, a constant
    // per level. Measured at the three smaller sizes, which bound it.
    if size <= 256 {
        let ((), cross_work) = crate::instrumentation::measure_deterministic_work(|| {
            let chain = Bitvector32Term::machine_integer_cast(last, Ty::Int32, chain.clone());
            assert!(!graph.are_int32_equal(&chain, &var(174_001)));
        });
        assert!(
            cross_work < 2600 * size as usize,
            "size={size}, cross={cross_work}"
        );
    }
    // Each half is linear in `size`. Measured (2026-11-03): about 36
    // units per independent cast, about 790 per chain level (a
    // narrowing, a widening, a sum and its constant; most of it is
    // union-find root reads while the level's K7' and R-comp relations
    // close), and about 2220 per level for the `int32` widening of the
    // `uint32` chain.
    assert!(casts < 120 * size as usize, "size={size}, casts={casts}");
    assert!(
        chain_work < 1000 * size as usize,
        "size={size}, chain={chain_work}"
    );
}

// Run each size independently so the containment timeout measures one case.
#[test]
fn narrow_cast_words_intern_in_work_linear_in_the_casts_16() {
    assert_narrow_cast_work(16);
}

#[test]
fn narrow_cast_words_intern_in_work_linear_in_the_casts_64() {
    assert_narrow_cast_work(64);
}

#[test]
fn narrow_cast_words_intern_in_work_linear_in_the_casts_256() {
    assert_narrow_cast_work(256);
}

#[test]
fn narrow_cast_words_intern_in_work_linear_in_the_casts_512() {
    assert_narrow_cast_work(512);
}
