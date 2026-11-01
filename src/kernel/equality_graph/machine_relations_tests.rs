//! The cross-format relations R0, R-dist and R-comp in the e-graph
//! (`terms/machine_relations.rs`; `design/machine-integers.md`, Decisions,
//! 2026-10-29), at the conversions the term arena spells as nodes today:
//! the 64-bit reinterpretation, the low word, the extensions and the
//! conversions into 8 and 16 bits.

use super::*;
use crate::kernel::MachineIntegerType as Ty;
use crate::kernel::VerificationSession;

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

fn cast(source: Ty, destination: Ty, value: Bitvector32Term) -> Bitvector32Term {
    Bitvector32Term::machine_integer_cast(source, destination, value)
}

/// R-dist at the low word: the low word of a 64-bit sum, difference,
/// product or bitwise operation is the 32-bit operation of the low words,
/// whatever the operands' signedness.
#[test]
fn the_low_word_distributes_over_the_sign_free_64_bit_operators() {
    let _session = VerificationSession::enter();
    use crate::kernel::MachineBinaryOp as Op;
    for format in [Ty::Int64, Ty::UInt64] {
        for op in [
            Op::Add,
            Op::Subtract,
            Op::Multiply,
            Op::BitwiseAnd,
            Op::BitwiseOr,
            Op::BitwiseXor,
        ] {
            let (a, b) = (var(181_001), var(181_002));
            let wide = Bitvector32Term::machine_binary(format, op, a.clone(), b.clone());
            let low = Bitvector32Term::uint32_from_64(wide);
            let narrow = Bitvector32Term::machine_binary(
                Ty::Int32,
                op,
                Bitvector32Term::uint32_from_64(a),
                Bitvector32Term::uint32_from_64(b),
            );
            let graph = EqualityGraph::default();
            assert!(graph.are_int32_equal(&low, &narrow), "{format:?} {op:?}");
        }
    }
}

/// R-dist does not hold for division, remainder or the right shift, whose
/// results' low bits depend on the high bits; the rule leaves them alone.
#[test]
fn the_low_word_does_not_distribute_over_division_or_the_right_shift() {
    let _session = VerificationSession::enter();
    use crate::kernel::MachineBinaryOp as Op;
    for op in [Op::Divide, Op::Remainder, Op::ShiftRight] {
        let (a, b) = (var(181_011), var(181_012));
        let low = Bitvector32Term::uint32_from_64(Bitvector32Term::machine_binary(
            Ty::UInt64,
            op,
            a.clone(),
            b.clone(),
        ));
        let narrow = Bitvector32Term::machine_binary(
            Ty::UInt32,
            op,
            Bitvector32Term::uint32_from_64(a),
            Bitvector32Term::uint32_from_64(b),
        );
        let graph = EqualityGraph::default();
        assert!(!graph.are_int32_equal(&low, &narrow), "{op:?}");
    }
}

/// R-dist at the same width: the 64-bit unsigned reading of a signed sum
/// is the unsigned sum of the readings (σ distributes).
#[test]
fn the_64_bit_reinterpretation_distributes_over_a_sum() {
    let _session = VerificationSession::enter();
    let (a, b) = (var(181_021), var(181_022));
    let reinterpreted =
        Bitvector32Term::uint64_from_int64(Bitvector32Term::int64_add(a.clone(), b.clone()));
    let unsigned = Bitvector32Term::uint64_add(
        Bitvector32Term::uint64_from_int64(a),
        Bitvector32Term::uint64_from_int64(b),
    );
    let graph = EqualityGraph::default();
    assert!(graph.are_uint64_equal(&reinterpreted, &unsigned));
}

/// R-dist fires when a union brings the operator to the conversion: the
/// low word of `y` meets the sum of low words once `y == a + b` is known,
/// in either order of interning.
#[test]
fn the_low_word_of_a_value_learned_equal_to_a_sum_distributes() {
    let _session = VerificationSession::enter();
    for intern_first in [false, true] {
        let (a, b, y) = (var(181_031), var(181_032), var(181_033));
        let sum = Bitvector32Term::uint64_add(a.clone(), b.clone());
        let low_y = Bitvector32Term::uint32_from_64(y.clone());
        let low_sum = Bitvector32Term::add(
            Bitvector32Term::uint32_from_64(a),
            Bitvector32Term::uint32_from_64(b),
        );
        let mut graph = EqualityGraph::default();
        if intern_first {
            assert!(!graph.are_int32_equal(&low_y, &low_sum));
        }
        graph.add_uint64_equality(&y, &sum);
        assert!(graph.are_int32_equal(&low_y, &low_sum), "{intern_first}");
    }
}

/// R-dist into 8 bits: truncating a 32-bit sum keeps only its operands'
/// low bytes, so two sums whose left operands truncate alike truncate
/// alike, though the operands differ.
#[test]
fn a_narrow_truncation_of_a_sum_depends_only_on_the_operands_truncations() {
    let _session = VerificationSession::enter();
    for destination in [Ty::UInt8, Ty::Int8, Ty::UInt16, Ty::Int16] {
        let (a, c, b) = (var(181_041), var(181_042), var(181_043));
        let left = cast(
            Ty::UInt32,
            destination,
            Bitvector32Term::add(a.clone(), b.clone()),
        );
        let right = cast(
            Ty::UInt32,
            destination,
            Bitvector32Term::add(c.clone(), b.clone()),
        );
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_int32_equal(&left, &right), "{destination:?}");
        graph.add_int32_equality(
            &cast(Ty::UInt32, destination, a),
            &cast(Ty::UInt32, destination, c),
        );
        assert!(graph.are_int32_equal(&left, &right), "{destination:?}");
    }
}

/// A shift by a constant below the destination's width distributes; a
/// shift by more does not (its truncation is zero, not a narrow shift).
#[test]
fn a_narrow_truncation_distributes_over_a_short_left_shift_only() {
    let _session = VerificationSession::enter();
    for (count, distributes) in [(3u32, true), (9, false)] {
        let (a, c) = (var(181_051), var(181_052));
        let shifted = |value: Bitvector32Term| {
            cast(
                Ty::UInt32,
                Ty::UInt8,
                Bitvector32Term::shift_left(value, Bitvector32Term::Constant(count)),
            )
        };
        let mut graph = EqualityGraph::default();
        graph.add_int32_equality(
            &cast(Ty::UInt32, Ty::UInt8, a.clone()),
            &cast(Ty::UInt32, Ty::UInt8, c.clone()),
        );
        assert_eq!(
            graph.are_int32_equal(&shifted(a), &shifted(c)),
            distributes,
            "count {count}"
        );
    }
}

/// R-comp: the low word of a value known to be a sign or zero extension is
/// the extended value, and a truncation of a value known to be a
/// truncation is one truncation. (The constructors compose a conversion of
/// a conversion they are given; the rule composes through a class.)
#[test]
fn conversions_compose_through_a_class() {
    let _session = VerificationSession::enter();
    let x = var(181_061);
    for extended in [
        Bitvector32Term::int64_from_32(x.clone()),
        Bitvector32Term::uint64_from_32(x.clone()),
    ] {
        let y = var(181_062);
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_int32_equal(&Bitvector32Term::uint32_from_64(y.clone()), &x));
        graph.add_uint64_equality(&y, &extended);
        assert!(graph.are_int32_equal(&Bitvector32Term::uint32_from_64(y), &x));
    }
    // `y` is a 16-bit value, equated at its width; the two byte casts are
    // 8-bit values compared at theirs.
    let y = var(181_063);
    let graph = EqualityGraph::default();
    let mut state = graph.state.lock().expect("equality graph");
    state.terms.add_typed_equality(
        crate::kernel::CarrierWidth::Bits16,
        &y,
        &cast(Ty::UInt32, Ty::Int16, x.clone()),
    );
    assert!(state.terms.are_typed_equal(
        crate::kernel::CarrierWidth::Bits8,
        &cast(Ty::Int16, Ty::UInt8, y.clone()),
        &cast(Ty::UInt32, Ty::UInt8, x.clone())
    ));
    // A widening of a truncation keeps the truncation's sign, not the
    // operand's: it is not the operand's conversion. `z` is an 8-bit value.
    let z = var(181_064);
    state.terms.add_typed_equality(
        crate::kernel::CarrierWidth::Bits8,
        &z,
        &cast(Ty::UInt32, Ty::UInt8, x.clone()),
    );
    assert!(!state.terms.are_typed_equal(
        crate::kernel::CarrierWidth::Bits16,
        &cast(Ty::UInt8, Ty::Int16, z),
        &cast(Ty::UInt32, Ty::Int16, x)
    ));
}

/// R0 does not invert a narrow conversion: a narrow operand's word need not
/// be its format's canonical carrier, and the conversion reads only its low
/// bits, so equal conversions do not make their operands equal
/// (`one_byte_one_name_tests` holds the byte read's own rule to this).
#[test]
fn a_narrow_same_width_conversion_is_not_inverted() {
    let _session = VerificationSession::enter();
    for (source, destination) in [(Ty::Int16, Ty::UInt16), (Ty::UInt8, Ty::Int8)] {
        let (a, b) = (var(181_071), var(181_072));
        let mut graph = EqualityGraph::default();
        graph.add_int32_equality(
            &cast(source, destination, a.clone()),
            &cast(source, destination, b.clone()),
        );
        assert!(
            !graph.are_int32_equal(&a, &b),
            "{source:?} -> {destination:?}"
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/machine_relations_tests.rs");
}

#[test]
fn wide_cast_composition_is_an_equality_without_erasing_the_terms() {
    let _session = VerificationSession::enter();
    for source in [Ty::Int32, Ty::UInt32, Ty::Int64, Ty::UInt64] {
        let original = var(189_001);
        let wide = cast(source, Ty::UInt128, original.clone());
        let signed = cast(Ty::UInt128, Ty::Int128, wide);
        let restored = cast(Ty::Int128, source, signed);
        assert_ne!(restored, original, "the cast structure must survive");
        let graph = EqualityGraph::default();
        let equal = if source.format().bits() == 32 {
            graph.are_int32_equal(&restored, &original)
        } else {
            graph.are_uint64_equal(&restored, &original)
        };
        assert!(equal, "{source:?}");
    }
    // A narrow intermediate loses bits. Widening afterwards cannot restore
    // equality with an arbitrary original 64-bit value.
    let original = var(189_002);
    let narrow = cast(Ty::Int64, Ty::Int32, original.clone());
    let wide = cast(Ty::Int32, Ty::Int128, narrow);
    let restored = cast(Ty::Int128, Ty::Int64, wide);
    assert!(!EqualityGraph::default().are_uint64_equal(&restored, &original));
}

#[test]
fn explicit_wide_add_sub_nodes_cancel_in_the_comparison_graph() {
    let _session = VerificationSession::enter();
    use crate::kernel::MachineBinaryOp as Op;
    for format in [Ty::Int64, Ty::UInt64] {
        let base = var(989_779);
        let literal = |n| {
            crate::kernel::machine_integer::range::constant_word(
                format,
                &num_bigint::BigInt::from(n),
            )
            .unwrap()
        };
        let sum =
            Bitvector32Term::logical_machine_binary(format, Op::Add, base.clone(), literal(1));
        let difference = |n| {
            Bitvector32Term::logical_machine_binary(format, Op::Subtract, sum.clone(), literal(n))
        };
        let graph = EqualityGraph::default();
        for (op, left, right, expected) in [
            (Op::Add, literal(0), base.clone(), base.clone()),
            (Op::Add, base.clone(), literal(0), base.clone()),
            (Op::Subtract, base.clone(), literal(0), base.clone()),
            (Op::Subtract, base.clone(), base.clone(), literal(0)),
            (Op::Multiply, base.clone(), literal(0), literal(0)),
            (Op::Multiply, base.clone(), literal(1), base.clone()),
        ] {
            let term = Bitvector32Term::logical_machine_binary(format, op, left, right);
            assert!(graph.are_uint64_equal(&term, &expected));
            assert!(matches!(term, Bitvector32Term::Binary { .. }));
        }
        assert!(graph.are_uint64_equal(&difference(1), &base));
        assert!(!graph.are_uint64_equal(&difference(2), &base));
        assert!(
            matches!(
                difference(1),
                Bitvector32Term::Binary {
                    op: Op::Subtract,
                    ..
                }
            ),
            "the comparison identity must not replace the term"
        );
    }
}
