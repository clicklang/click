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
                side = MachineTerm::machine_binary(format, Op::Add, side, var(20_000 + index));
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
        let mut chain = MachineTerm::machine_integer_cast(Ty::UInt32, formats[0], operand.clone());
        let mut bits: u128 = 0x1f0 & 0xff;
        let mut last = formats[0];
        for index in 1..depth {
            let next = formats[index as usize % formats.len()];
            let link = var(40_000 + index);
            state
                .terms
                .add_typed_equality(W::of_machine_type(last), &link, &chain);
            chain = MachineTerm::machine_integer_cast(last, next, link);
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
        let expected = MachineTerm::narrow_constant(last, bits);
        assert!(!state.terms.are_typed_equal(width, &chain, &expected));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            state
                .terms
                .add_typed_equality(W::Bits32, &operand, &MachineTerm::constant(0x1f0));
            assert!(
                state.terms.are_typed_equal(width, &chain, &expected),
                "depth {depth}: {last:?} {bits:#x}"
            );
        });
        samples.push(work);
    }
    assert_constant_step("narrow cast chain", &samples);
}

#[test]
fn narrow_store_equation_queries_do_not_walk_alias_classes_or_unrelated_cells() {
    narrow_store_equation_query_scaling([1, 4, 8, 16]);
}

#[test]
#[ignore = "nightly: 9s parallel, large narrow-store query histories across all formats and alias patterns"]
fn narrow_store_equation_queries_with_large_histories() {
    narrow_store_equation_query_scaling([16, 64, 256, 1024]);
}

fn narrow_store_equation_query_scaling(sizes: [u64; 4]) {
    for format in [Ty::Int8, Ty::UInt8, Ty::Int16, Ty::UInt16] {
        for related in [false, true] {
            let mut samples = Vec::new();
            for size in sizes {
                let _session = crate::kernel::VerificationSession::enter();
                let cell = |i| Address {
                    base: "narrow".into(),
                    offset: AddressOffset::Constant(i * 4),
                };
                let stored = narrow_stored_value(format, 7);
                let mut memory = SymbolicMemory::new().with_block("narrow", (size as u32 + 1) * 4);
                let mut facts = PureFactContext::new();
                for i in 1..=size {
                    memory = memory.store(cell(i as i64), narrow_stored_value(format, 3));
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_equal(
                            Address::symbolic(Variable(995000 + i)),
                            if related { cell(0) } else { cell(i as i64) },
                        ),
                        true,
                    );
                }
                memory = memory.store(cell(0), stored.clone());
                let query = Address::symbolic(Variable(999999));
                facts = facts
                    .assume_condition(ConditionTerm::pointer_equal(query.clone(), cell(0)), true);
                facts = facts.assume_proposition(
                    crate::kernel::memory_history::store_value_equation(&memory, &cell(0), &stored)
                        .unwrap(),
                );
                let memory = intern_memory(memory);
                let kind = LoadKind::of_value(&stored).unwrap();
                let read = crate::kernel::eval::scalar_read_for_exact_cell(
                    &memory,
                    &query,
                    kind,
                    kind.byte_width(),
                );
                let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
                    narrow_equal(&facts.equality_graph, format, &read, &constant(format, 7))
                });
                assert!(ok, "{format:?}, related={related}, size={size}");
                samples.push(work);
            }
            assert!(
                samples.windows(2).all(|p| p[0] == p[1]),
                "{format:?}, related={related}: {samples:?}"
            );
        }
    }
}
