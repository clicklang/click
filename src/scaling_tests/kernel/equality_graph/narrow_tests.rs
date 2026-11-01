// Scaling tests of `src/kernel/equality_graph/narrow_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, ConditionTerm};

const DEPTHS: [u64; 4] = [8, 32, 128, 512];

/// The work added per element, which must be about the same at every size
/// step.
fn assert_constant_step(name: &str, samples: &[usize]) {
    assert!(
        samples[0] > 0 && samples[3] > samples[0],
        "{name}: {samples:?}"
    );
    let step = |i: usize| (samples[i + 1] - samples[i]) as f64 / (DEPTHS[i + 1] - DEPTHS[i]) as f64;
    // Within a tenth of the first step: union-find bookkeeping varies a
    // little with the classes' sizes.
    for i in 1..DEPTHS.len() - 1 {
        assert!(
            (step(i) - step(0)).abs() <= step(0) / 10.0,
            "{name}: {samples:?}"
        );
    }
}

/// A 32-bit equation whose side is an 8- or 16-bit value is interned at
/// the side's width, read from the sides' roots (`root_width`): the width
/// reads per interned equation stay the same however deep its sides are,
/// and its decision costs work linear in the sides' size. A recursive width
/// check (`term_width`) would read every node of both sides.
#[test]
fn narrow_equation_width_reads_are_root_bounded() {
    let _session = crate::kernel::VerificationSession::enter();
    for (format, width) in [(Ty::UInt8, W::Bits8), (Ty::Int16, W::Bits16)] {
        let mut reads = Vec::new();
        let mut samples = Vec::new();
        for depth in DEPTHS {
            let mut side = var(20_000);
            for index in 1..depth {
                side = Bitvector32Term::machine_binary(format, Op::Add, side, var(20_000 + index));
            }
            let equation = |right| ConditionTerm::Compare {
                format: Ty::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(side.clone()),
                right: Box::new(var(right)),
            };
            let graph = EqualityGraph::default();
            let mut state = graph.state.lock().expect("equality graph");
            state
                .terms
                .add_typed_equality(width, &side, &var(90_000 + depth));
            crate::kernel::WIDTH_NODE_READS.with(|reads| reads.set(0));
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                // Decided by the condition's truth, then by the sides'
                // classes (`narrow_equation`).
                assert!(state.terms.knows_condition(&equation(90_000 + depth), true));
                assert!(!state.terms.knows_condition(&equation(91_000 + depth), true));
            });
            reads.push(crate::kernel::WIDTH_NODE_READS.with(|reads| reads.get()));
            samples.push(work);
        }
        assert!(
            reads.iter().all(|&count| count == reads[0] && count <= 6),
            "{format:?}: width reads {reads:?}"
        );
        assert_constant_step(&format!("{format:?} equation"), &samples);
    }
}

/// A chain of `n` casts between narrow formats over a 32-bit operand folds
/// to its constant when the operand learns one late: each cast's operand is
/// a variable equated with the previous cast (so the cast constructor cannot
/// compose them), each cast folds once from its operand class's constant,
/// and the learning costs work linear in `n`. The chain's last cast is the
/// constant its bits give.
#[test]
fn narrow_cast_chains_fold_a_late_constant_in_linear_work() {
    let _session = crate::kernel::VerificationSession::enter();
    // A cycle of sign casts, a narrowing and a widening through every
    // narrow format.
    let formats = [Ty::UInt8, Ty::Int8, Ty::Int16, Ty::UInt16];
    let mut samples = Vec::new();
    for depth in DEPTHS {
        let graph = EqualityGraph::default();
        let mut state = graph.state.lock().expect("equality graph");
        let operand = var(30_000);
        let mut chain =
            Bitvector32Term::machine_integer_cast(Ty::UInt32, formats[0], operand.clone());
        let mut bits: u128 = 0x1f0 & 0xff;
        let mut last = formats[0];
        for index in 1..depth {
            let next = formats[index as usize % formats.len()];
            let link = var(40_000 + index);
            state
                .terms
                .add_typed_equality(W::of_machine_type(last), &link, &chain);
            chain = Bitvector32Term::machine_integer_cast(last, next, link);
            // The cast's bits: the source's value at the destination's width.
            let source_bits = last.format().bits();
            let value = if last.format().is_signed() && bits >> (source_bits - 1) & 1 == 1 {
                bits | !((1u128 << source_bits) - 1)
            } else {
                bits
            };
            bits = value & ((1u128 << next.format().bits()) - 1);
            last = next;
        }
        let width = W::of_machine_type(last);
        let expected = Bitvector32Term::narrow_constant(last, bits);
        assert!(!state.terms.are_typed_equal(width, &chain, &expected));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            state
                .terms
                .add_typed_equality(W::Bits32, &operand, &Bitvector32Term::Constant(0x1f0));
            assert!(
                state.terms.are_typed_equal(width, &chain, &expected),
                "depth {depth}: {last:?} {bits:#x}"
            );
        });
        samples.push(work);
    }
    assert_constant_step("narrow cast chain", &samples);
}
