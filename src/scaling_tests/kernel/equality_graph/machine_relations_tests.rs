// Scaling tests of `src/kernel/equality_graph/machine_relations_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

const SIZES: [u64; 4] = [16, 64, 256, 1024];

/// Work at each of [`SIZES`] grows at most linearly: from one size to the
/// next, by no more than `slope` units per added element.
fn assert_linear(name: &str, work: &[usize], slope: usize) {
    for (pair, sizes) in work.windows(2).zip(SIZES.windows(2)) {
        let added = (sizes[1] - sizes[0]) as usize;
        assert!(
            pair[1] <= pair[0] + slope * added,
            "{name}: {} -> {} elements cost {} -> {}",
            sizes[0],
            sizes[1],
            pair[0],
            pair[1]
        );
    }
}

/// A chain of `size` 64-bit signed operations under its unsigned reading,
/// and the unsigned chain over the operands' readings.
fn reinterpreted_chain(size: u64) -> (Bitvector32Term, Bitvector32Term) {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [Op::Add, Op::Multiply, Op::BitwiseXor, Op::Subtract];
    let mut signed = var(182_000);
    let mut unsigned = Bitvector32Term::uint64_from_int64(var(182_000));
    for index in 0..size {
        let op = ops[index as usize % ops.len()];
        let operand = var(182_001 + index);
        signed = Bitvector32Term::machine_binary(Ty::Int64, op, signed, operand.clone());
        unsigned = Bitvector32Term::machine_binary(
            Ty::UInt64,
            op,
            unsigned,
            Bitvector32Term::uint64_from_int64(operand),
        );
    }
    (Bitvector32Term::uint64_from_int64(signed), unsigned)
}

/// σ over a chain of `n` operations distributes in work linear in `n`:
/// each conversion meets one operator once, and each operand's conversion
/// is interned once.
#[test]
fn sign_cast_distribution_is_linear_in_the_operation_chain() {
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let (reinterpreted, unsigned) = reinterpreted_chain(size);
        let (equal, units) = crate::instrumentation::measure_deterministic_work(|| {
            EqualityGraph::default().are_uint64_equal(&reinterpreted, &unsigned)
        });
        assert!(equal, "size {size}");
        work.push(units);
    }
    assert_linear("σ distribution", &work, 60);
}

/// `n` low words interned before `n` facts `y == a + b` make them sums:
/// each union fires its class's conversions once, so the facts and the
/// queries cost linear work, not one pass over every conversion per fact.
#[test]
fn class_triggered_distribution_scales_with_merges() {
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let ((), units) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            let value = |index: u64, slot: u64| var(183_000 + 3 * index + slot);
            for index in 0..size {
                let low = Bitvector32Term::uint32_from_64(value(index, 0));
                assert!(!graph.are_int32_equal(&low, &value(index, 1)));
            }
            for index in 0..size {
                let sum = Bitvector32Term::uint64_add(value(index, 1), value(index, 2));
                graph.add_uint64_equality(&value(index, 0), &sum);
            }
            for index in 0..size {
                let low = Bitvector32Term::uint32_from_64(value(index, 0));
                let sum = Bitvector32Term::add(
                    Bitvector32Term::uint32_from_64(value(index, 1)),
                    Bitvector32Term::uint32_from_64(value(index, 2)),
                );
                assert!(graph.are_int32_equal(&low, &sum), "size {size}, {index}");
            }
        });
        work.push(units);
    }
    assert_linear("merge-triggered distribution", &work, 80);
}

/// A truncation into 8 bits of a chain of `n` 32-bit operations meets the
/// truncation of the same chain over an operand with the same low byte in
/// work linear in `n`.
#[test]
fn truncation_of_promoted_arithmetic_is_linear() {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [
        Op::Add,
        Op::Multiply,
        Op::BitwiseXor,
        Op::Subtract,
        Op::BitwiseAnd,
    ];
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let chain = |base: Bitvector32Term| {
            let mut term = base;
            for index in 0..size {
                let op = ops[index as usize % ops.len()];
                term = Bitvector32Term::machine_binary(Ty::Int32, op, term, var(184_010 + index));
            }
            cast(Ty::UInt32, Ty::UInt8, term)
        };
        let (a, c) = (var(184_000), var(184_001));
        let (left, right) = (chain(a.clone()), chain(c.clone()));
        let ((), units) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            graph.add_int32_equality(
                &cast(Ty::UInt32, Ty::UInt8, a.clone()),
                &cast(Ty::UInt32, Ty::UInt8, c.clone()),
            );
            assert!(graph.are_int32_equal(&left, &right), "size {size}");
        });
        work.push(units);
    }
    assert_linear("narrow truncation", &work, 150);
}
