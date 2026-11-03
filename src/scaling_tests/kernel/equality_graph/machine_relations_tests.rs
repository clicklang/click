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
    // About 211 units per element at every size step (measured
    // 2026-10-31). Each level of each chain interns, beside its 32-bit
    // operator, a native 8-bit cast of its own width, the R-dist 8-bit
    // operator over the casts of its operands, and for each new cast its
    // `int32` and `uint32` widenings joined with its rule-K7' masked word.
    // Under the former 32-bit carrier the cast was one node joined with its
    // word, so the slope was below 150. The added work is those nodes'
    // interning, unions and reindexing, constant per node.
    assert_linear("narrow truncation", &work, 230);
}

#[test]
fn wide_cast_composition_scales_with_selected_chain_not_unrelated_classes() {
    for unrelated in [0, 128, 512] {
        for size in [16, 64, 256] {
            let _session = VerificationSession::enter();
            let mut graph = EqualityGraph::default();
            for i in 0..unrelated {
                graph.add_int32_equality(&var(195_000 + 2 * i), &var(195_001 + 2 * i));
            }
            let original = var(196_100);
            let mut term = cast(Ty::Int64, Ty::UInt128, original.clone());
            let mut format = Ty::UInt128;
            for _ in 0..size {
                let destination = if format == Ty::UInt128 {
                    Ty::Int128
                } else {
                    Ty::UInt128
                };
                term = cast(format, destination, term);
                format = destination;
            }
            let restored = cast(format, Ty::Int64, term);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.are_uint64_equal(&restored, &original)
            });
            assert!(equal);
            assert!(
                work <= 128 * (size + 1),
                "size={size}, unrelated={unrelated}, work={work}"
            );
        }
    }
}

/// A chain of `size` native `uint8` operations, and C's spelling of the same
/// chain: each step promoted to `int32` and narrowed back.
fn narrow_chain(size: u64) -> (Bitvector32Term, Bitvector32Term) {
    use crate::kernel::MachineBinaryOp as Op;
    // Not `^`: the 32-bit constructor flattens and orders an exclusive-or
    // chain, so C's spelling of a chain is not the narrow chain's shape.
    let ops = [Op::Add, Op::Multiply, Op::Subtract];
    let mut native = var(184_000);
    let mut promoted = var(184_000);
    for index in 0..size {
        let op = ops[index as usize % ops.len()];
        let operand = var(184_001 + index);
        native = Bitvector32Term::machine_binary(Ty::UInt8, op, native, operand.clone());
        promoted = cast(
            Ty::Int32,
            Ty::UInt8,
            Bitvector32Term::machine_binary(
                Ty::Int32,
                op,
                cast(Ty::UInt8, Ty::Int32, promoted),
                cast(Ty::UInt8, Ty::Int32, operand),
            ),
        );
    }
    (native, promoted)
}

/// Rule N fires once per native operator, and R-dist with R-comp once per
/// narrowing, so relating a chain of `n` native operators to its promoted
/// spelling costs work linear in `n`.
#[test]
fn native_narrow_promotion_is_linear_in_the_operation_chain() {
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let (native, promoted) = narrow_chain(size);
        let (equal, units) = crate::instrumentation::measure_deterministic_work(|| {
            let graph = EqualityGraph::default();
            let mut state = graph.state.lock().expect("equality graph");
            state
                .terms
                .are_typed_equal(crate::kernel::CarrierWidth::Bits8, &native, &promoted)
        });
        assert!(equal, "size {size}");
        work.push(units);
    }
    assert_linear("rule N", &work, 600);
}

/// Rule N fires where a native operator is widened: the widening of each of
/// `n` native `uint8` operators meets the masked 32-bit operator of its
/// operands' widenings (rule K7'). Each firing is constant work, so `n`
/// widened operators cost work linear in `n`.
#[test]
fn widened_native_narrow_operators_are_linear() {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [Op::Add, Op::Multiply, Op::Subtract, Op::ShiftLeft];
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let widen = |term: Bitvector32Term| cast(Ty::UInt8, Ty::Int32, term);
        let ((), units) = crate::instrumentation::measure_deterministic_work(|| {
            let graph = EqualityGraph::default();
            for index in 0..size {
                let op = ops[index as usize % ops.len()];
                let (a, b) = (var(185_000 + 2 * index), var(185_001 + 2 * index));
                let native = Bitvector32Term::machine_binary(Ty::UInt8, op, a.clone(), b.clone());
                let right = if op == Op::ShiftLeft { b } else { widen(b) };
                let masked = Bitvector32Term::machine_binary(
                    Ty::Int32,
                    Op::BitwiseAnd,
                    Bitvector32Term::machine_binary(Ty::Int32, op, widen(a), right),
                    Bitvector32Term::constant(255),
                );
                assert!(
                    graph.are_int32_equal(&widen(native), &masked),
                    "size {size} {op:?}"
                );
            }
        });
        work.push(units);
    }
    assert_linear("widened rule N", &work, 1000);
}

/// A chain of `size` 32-bit operations over `int32` operands and the same
/// chain at `uint32` over the operands' σ: σ of the first is the second.
fn sign_cast32_chain(size: u64) -> (Bitvector32Term, Bitvector32Term) {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [Op::Add, Op::Multiply, Op::BitwiseAnd, Op::Subtract];
    let sigma = |value| Bitvector32Term::sign_cast32(Ty::Int32, Ty::UInt32, value);
    let mut signed = var(186_000);
    let mut unsigned = sigma(var(186_000));
    for index in 0..size {
        let op = ops[index as usize % ops.len()];
        let operand = var(186_001 + index);
        signed = Bitvector32Term::machine_binary(Ty::Int32, op, signed, operand.clone());
        unsigned = Bitvector32Term::machine_binary(Ty::UInt32, op, unsigned, sigma(operand));
    }
    (sigma(signed), unsigned)
}

/// σ over a chain of `n` 32-bit operations meets the `uint32` chain over
/// its operands' σ in work linear in `n`, at a bounded constant per
/// operation: each σ meets one operator once (R-dist), and each σ the rule
/// interns is inverted once (R0) and composed once with the σ it inverts
/// (R-comp). Measured 2026-11-02: about 174 units per operation at every
/// size step, against about 53 for the 64-bit reinterpretation
/// (`sign_cast_distribution_is_linear_in_the_operation_chain`), whose
/// inverse is the word itself and interns no node. The bound below is
/// per operation, so a constant blowup fails it at every size.
#[test]
fn sign_cast32_distribution_is_linear_in_the_operation_chain() {
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let (cast_chain, unsigned) = sign_cast32_chain(size);
        let (equal, units) = crate::instrumentation::measure_deterministic_work(|| {
            EqualityGraph::default().are_int32_equal(&cast_chain, &unsigned)
        });
        assert!(equal, "size {size}");
        assert!(
            units <= 200 * (size as usize + 1),
            "size {size}: {units} units"
        );
        work.push(units);
    }
    assert_linear("σ distribution at 32 bits", &work, 200);
}

/// R0 at 32 bits: `n` facts `u_i == σ(x_i)` answer `σ(u_i) == x_i` with one
/// inversion each, so the facts and queries cost work linear in `n`, at a
/// constant per pair bounded by a few times the cost of the facts alone.
#[test]
fn sign_cast32_inverse_is_constant_work_per_cast() {
    let sigma = |source: Ty, destination: Ty, value| {
        Bitvector32Term::sign_cast32(source, destination, value)
    };
    let mut work = Vec::new();
    for size in SIZES {
        let _session = VerificationSession::enter();
        let pair = |index: u64| (var(187_000 + 2 * index), var(187_001 + 2 * index));
        // The same facts and queries with no σ: `u_i == x_i`.
        let ((), plain) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            for index in 0..size {
                let (u, x) = pair(index);
                graph.add_int32_equality(&u, &x);
                assert!(graph.are_int32_equal(&x, &u));
            }
        });
        let ((), units) = crate::instrumentation::measure_deterministic_work(|| {
            let mut graph = EqualityGraph::default();
            for index in 0..size {
                let (u, x) = pair(index);
                graph.add_int32_equality(&u, &sigma(Ty::Int32, Ty::UInt32, x.clone()));
                assert!(
                    graph.are_int32_equal(&sigma(Ty::UInt32, Ty::Int32, u), &x),
                    "size {size}, {index}"
                );
            }
        });
        assert!(
            units <= 8 * plain + 64,
            "size {size}: {units} units against {plain} for plain facts"
        );
        work.push(units);
    }
    assert_linear("σ inverse", &work, 120);
}

/// A chain of `n` 32-bit operations costs the same at `uint32` as at
/// `int32`: an operator of either format is one e-graph operator, so
/// deciding the chain over equal operands is the same work, linear in `n`.
#[test]
fn uint32_and_int32_chains_cost_alike() {
    use crate::kernel::MachineBinaryOp as Op;
    let ops = [
        Op::Add,
        Op::Multiply,
        Op::BitwiseXor,
        Op::Subtract,
        Op::BitwiseOr,
    ];
    let mut work = Vec::new();
    for size in SIZES {
        let mut units_at = Vec::new();
        for format in [Ty::Int32, Ty::UInt32] {
            let _session = VerificationSession::enter();
            let chain = |base: Bitvector32Term| {
                let mut term = base;
                for index in 0..size {
                    let op = ops[index as usize % ops.len()];
                    term = Bitvector32Term::machine_binary(format, op, term, var(188_010 + index));
                }
                term
            };
            let (a, b) = (var(188_000), var(188_001));
            let (left, right) = (chain(a.clone()), chain(b.clone()));
            let ((), units) = crate::instrumentation::measure_deterministic_work(|| {
                let mut graph = EqualityGraph::default();
                graph.add_int32_equality(&a, &b);
                assert!(
                    graph.are_int32_equal(&left, &right),
                    "{format:?} size {size}"
                );
            });
            units_at.push(units);
        }
        assert_eq!(
            units_at[0], units_at[1],
            "size {size}: int32 and uint32 chains"
        );
        work.push(units_at[1]);
    }
    assert_linear("uint32 chain", &work, 60);
}
