//! The one map between a format and the term nodes that spell it today.
//!
//! The term arena records no width (`docs/internals/kernel.md`, "Important
//! types"): a 32-bit operation is `Add`, a 64-bit one `Int64Add` or
//! `UInt64Add`, and values of 8 and 16 bits ride in the 32-bit word as
//! their sign or zero extension. Rules ask this module for the node of an
//! operation, comparison or overflow test at a format, or for the format
//! and operation a node spells, and never match on a width themselves.
//!
//! Where a format has no node the answer is `None`, and the rule is
//! unavailable there: there are no 128-bit operators or comparisons, no
//! unsigned or narrow overflow tests, and no 32-bit unsigned order other
//! than the signed order of operands whose sign bit is flipped. These are
//! the representation gaps that `design/machine-integers.md` Stages 2 and 3
//! remove; the test matrix names each one.

use super::{Operation, Relation};
use crate::kernel::{Bitvector32Term, ConditionTerm, MachineIntegerType};

/// The word a format's values ride in, which decides its nodes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Word {
    /// 8, 16 and 32 bits: the 32-bit word, a narrow value as its canonical
    /// extension.
    Bits32,
    /// `int64`.
    Signed64,
    /// `uint64`.
    Unsigned64,
    /// 128 bits: constants, variables, loads and casts only.
    Bits128,
}

fn word(ty: MachineIntegerType) -> Word {
    let format = ty.format();
    match (format.bits(), format.is_signed()) {
        (8 | 16 | 32, _) => Word::Bits32,
        (64, true) => Word::Signed64,
        (64, false) => Word::Unsigned64,
        _ => Word::Bits128,
    }
}

/// The width of the word whose arithmetic `ty`'s ring operations reduce
/// modulo: 32 for 8-, 16- and 32-bit formats, whose operations are 32-bit
/// word operations, 64 for 64-bit formats, and `None` at 128 bits, which has
/// no operations.
pub(crate) fn word_bits(ty: MachineIntegerType) -> Option<u32> {
    match word(ty) {
        Word::Bits32 => Some(32),
        Word::Signed64 | Word::Unsigned64 => Some(64),
        Word::Bits128 => None,
    }
}

/// The machine operation `left op right` at `ty`, as the node the term
/// arena spells it with, unsimplified. `None` where `ty` has no such node.
pub(crate) fn operation_word(
    ty: MachineIntegerType,
    operation: Operation,
    left: Box<Bitvector32Term>,
    right: Box<Bitvector32Term>,
) -> Option<Bitvector32Term> {
    use Bitvector32Term as T;
    Some(match (word(ty), operation) {
        (Word::Bits32, Operation::Add) => T::Add(left, right),
        (Word::Bits32, Operation::Subtract) => T::Subtract(left, right),
        (Word::Bits32, Operation::Multiply) => T::Multiply(left, right),
        (Word::Signed64, Operation::Add) => T::Int64Add(left, right),
        (Word::Signed64, Operation::Subtract) => T::Int64Subtract(left, right),
        (Word::Signed64, Operation::Multiply) => T::Int64Multiply(left, right),
        (Word::Unsigned64, Operation::Add) => T::UInt64Add(left, right),
        (Word::Unsigned64, Operation::Subtract) => T::UInt64Subtract(left, right),
        (Word::Unsigned64, Operation::Multiply) => T::UInt64Multiply(left, right),
        (Word::Bits128, _) => return None,
    })
}

/// The machine operation `left op right` at `ty`, built by the folding
/// constructors (`Bitvector32Term::add`, `int64_add`, ...), which simplify
/// constant operands. `None` where `ty` has no such node.
pub(crate) fn folded_operation_word(
    ty: MachineIntegerType,
    operation: Operation,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Option<Bitvector32Term> {
    use Bitvector32Term as T;
    Some(match (word(ty), operation) {
        (Word::Bits32, Operation::Add) => T::add(left, right),
        (Word::Bits32, Operation::Subtract) => T::subtract(left, right),
        (Word::Bits32, Operation::Multiply) => T::multiply(left, right),
        (Word::Signed64, Operation::Add) => T::int64_add(left, right),
        (Word::Signed64, Operation::Subtract) => T::int64_subtract(left, right),
        (Word::Signed64, Operation::Multiply) => T::int64_multiply(left, right),
        (Word::Unsigned64, Operation::Add) => T::uint64_add(left, right),
        (Word::Unsigned64, Operation::Subtract) => T::uint64_subtract(left, right),
        (Word::Unsigned64, Operation::Multiply) => T::uint64_multiply(left, right),
        (Word::Bits128, _) => return None,
    })
}

/// The operation and operands of `value`, a word read at `ty`, when it is a
/// machine `+`, `-` or `*` at `ty`.
pub(crate) fn word_operation(
    ty: MachineIntegerType,
    value: &Bitvector32Term,
) -> Option<(Operation, &Bitvector32Term, &Bitvector32Term)> {
    use Bitvector32Term as T;
    let (operation, left, right) = match (word(ty), value) {
        (Word::Bits32, T::Add(left, right))
        | (Word::Signed64, T::Int64Add(left, right))
        | (Word::Unsigned64, T::UInt64Add(left, right)) => (Operation::Add, left, right),
        (Word::Bits32, T::Subtract(left, right))
        | (Word::Signed64, T::Int64Subtract(left, right))
        | (Word::Unsigned64, T::UInt64Subtract(left, right)) => (Operation::Subtract, left, right),
        (Word::Bits32, T::Multiply(left, right))
        | (Word::Signed64, T::Int64Multiply(left, right))
        | (Word::Unsigned64, T::UInt64Multiply(left, right)) => (Operation::Multiply, left, right),
        _ => return None,
    };
    Some((operation, left, right))
}

/// Whether `value` is a machine `+`, `-` or `*` at any format.
pub(crate) fn is_ring_operation(value: &Bitvector32Term) -> bool {
    [
        MachineIntegerType::Int32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ]
    .into_iter()
    .any(|ty| word_operation(ty, value).is_some())
}

/// The native comparison `left REL right` at `ty`, with the truth it is
/// filed at (`!=` is a false equality), built by the folding constructors.
/// A narrow value's word is its canonical extension, which the signed
/// 32-bit order compares exactly, as C's promotion to `int` does.
pub(crate) fn comparison(
    ty: MachineIntegerType,
    relation: Relation,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Option<(ConditionTerm, bool)> {
    let unsigned32 = ty == MachineIntegerType::UInt32;
    let condition = match (word(ty), relation) {
        (Word::Bits32, Relation::Less) if unsigned32 => {
            ConditionTerm::unsigned_less_than(left, right)
        }
        (Word::Bits32, Relation::Less) => ConditionTerm::signed_less_than(left, right),
        (Word::Bits32, Relation::LessEqual) if unsigned32 => {
            ConditionTerm::unsigned_less_equal(left, right)
        }
        (Word::Bits32, Relation::LessEqual) => ConditionTerm::signed_less_equal(left, right),
        (Word::Bits32, Relation::Equal | Relation::NotEqual) => ConditionTerm::equal(left, right),
        (Word::Signed64, Relation::Less) => ConditionTerm::int64_signed_less_than(left, right),
        (Word::Signed64, Relation::LessEqual) => {
            ConditionTerm::int64_signed_less_equal(left, right)
        }
        (Word::Signed64, Relation::Equal | Relation::NotEqual) => {
            ConditionTerm::int64_equal(left, right)
        }
        (Word::Unsigned64, Relation::Less) => ConditionTerm::uint64_less_than(left, right),
        (Word::Unsigned64, Relation::LessEqual) => ConditionTerm::uint64_less_equal(left, right),
        (Word::Unsigned64, Relation::Equal | Relation::NotEqual) => {
            ConditionTerm::uint64_equal(left, right)
        }
        (Word::Bits128, _) => return None,
    };
    Some((condition, relation != Relation::NotEqual))
}

/// The operands of a native comparison and the formats whose exact reading
/// it may be, most specific first. A 32-bit order is signed, or a `uint32`
/// order of operands whose sign bit is flipped (`order_operand` strips the
/// flip); a narrow value reads through the `int32` reading, which
/// `IntegerTerm::from_machine` normalizes to the narrow observation.
pub(crate) fn comparison_readings(
    condition: &ConditionTerm,
) -> Option<(
    &Bitvector32Term,
    &Bitvector32Term,
    &'static [MachineIntegerType],
)> {
    use ConditionTerm as C;
    use MachineIntegerType as Ty;
    Some(match condition {
        // A `uint32` order is the signed order of sign-flipped operands,
        // so its own reading comes first; a genuinely signed order has no
        // sign-bit encoding to strip and reads as `int32`.
        C::Bitvector32SignedLessThan(left, right)
        | C::Bitvector32SignedLessEqual(left, right)
        | C::Bitvector32SignedGreaterThan(left, right)
        | C::Bitvector32SignedGreaterEqual(left, right) => (left, right, &[Ty::UInt32, Ty::Int32]),
        C::Bitvector32Equal(left, right) => (left, right, &[Ty::Int32, Ty::UInt32]),
        C::Bitvector64SignedLessThan(left, right)
        | C::Bitvector64SignedLessEqual(left, right)
        | C::Bitvector64SignedGreaterThan(left, right)
        | C::Bitvector64SignedGreaterEqual(left, right) => (left, right, &[Ty::Int64]),
        C::Bitvector64Equal(left, right) => (left, right, &[Ty::Int64, Ty::UInt64]),
        C::Bitvector64UnsignedLessThan(left, right)
        | C::Bitvector64UnsignedLessEqual(left, right)
        | C::Bitvector64UnsignedGreaterThan(left, right)
        | C::Bitvector64UnsignedGreaterEqual(left, right) => (left, right, &[Ty::UInt64]),
        _ => return None,
    })
}

/// The word a native comparison at `ty` compares, before its encoding: a
/// `uint32` order compares its operands with the sign bit flipped, so the
/// flip is removed; any other comparison compares its operands as they are.
/// `None` when a `uint32` order's operand carries no flip.
pub(crate) fn order_operand(
    ty: MachineIntegerType,
    condition: &ConditionTerm,
    side: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    if ty != MachineIntegerType::UInt32 || matches!(condition, ConditionTerm::Bitvector32Equal(..))
    {
        return Some(side.clone());
    }
    let sign_bit = 0x8000_0000u32;
    match side {
        Bitvector32Term::Constant(value) => Some(Bitvector32Term::Constant(value ^ sign_bit)),
        Bitvector32Term::BitwiseXor(a, b) => match (a.as_ref(), b.as_ref()) {
            (Bitvector32Term::Constant(bit), other) | (other, Bitvector32Term::Constant(bit))
                if *bit == sign_bit =>
            {
                Some(other.clone())
            }
            _ => None,
        },
        _ => None,
    }
}

/// Whether `ty` has an overflow test for `+`, `-` and `*`
/// ([`overflow_condition`]); a constant-time check, with no node built.
pub(crate) fn has_overflow_test(ty: MachineIntegerType) -> bool {
    matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::Int64)
}

/// The overflow test of `left op right` at `ty`, as the unsimplified node
/// a definedness fact files. `None` where `ty` has no overflow test: only
/// `int32` and `int64` have one today.
pub(crate) fn overflow_condition(
    ty: MachineIntegerType,
    operation: Operation,
    left: Box<Bitvector32Term>,
    right: Box<Bitvector32Term>,
) -> Option<ConditionTerm> {
    use ConditionTerm as C;
    Some(match (ty, operation) {
        (MachineIntegerType::Int32, Operation::Add) => {
            C::Bitvector32SignedAddOverflows(left, right)
        }
        (MachineIntegerType::Int32, Operation::Subtract) => {
            C::Bitvector32SignedSubtractOverflows(left, right)
        }
        (MachineIntegerType::Int32, Operation::Multiply) => {
            C::Bitvector32SignedMultiplyOverflows(left, right)
        }
        (MachineIntegerType::Int64, Operation::Add) => {
            C::Bitvector64SignedAddOverflows(left, right)
        }
        (MachineIntegerType::Int64, Operation::Subtract) => {
            C::Bitvector64SignedSubtractOverflows(left, right)
        }
        (MachineIntegerType::Int64, Operation::Multiply) => {
            C::Bitvector64SignedMultiplyOverflows(left, right)
        }
        _ => return None,
    })
}

/// The format, operation and operands of an overflow test of `+`, `-` or
/// `*`.
pub(crate) fn overflow_operation(
    condition: &ConditionTerm,
) -> Option<(
    MachineIntegerType,
    Operation,
    &Bitvector32Term,
    &Bitvector32Term,
)> {
    use ConditionTerm as C;
    use MachineIntegerType as Ty;
    let (ty, operation, left, right) = match condition {
        C::Bitvector32SignedAddOverflows(left, right) => (Ty::Int32, Operation::Add, left, right),
        C::Bitvector32SignedSubtractOverflows(left, right) => {
            (Ty::Int32, Operation::Subtract, left, right)
        }
        C::Bitvector32SignedMultiplyOverflows(left, right) => {
            (Ty::Int32, Operation::Multiply, left, right)
        }
        C::Bitvector64SignedAddOverflows(left, right) => (Ty::Int64, Operation::Add, left, right),
        C::Bitvector64SignedSubtractOverflows(left, right) => {
            (Ty::Int64, Operation::Subtract, left, right)
        }
        C::Bitvector64SignedMultiplyOverflows(left, right) => {
            (Ty::Int64, Operation::Multiply, left, right)
        }
        _ => return None,
    };
    Some((ty, operation, left, right))
}

/// A truncating quotient, floor right shift or remainder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Division {
    /// `x / d`, truncated toward zero.
    Quotient,
    /// `x >> k`: the floor of `x / 2^k`.
    ShiftRight,
    /// `x % d`, with the sign of `x`.
    Remainder,
}

/// The division, operand and divisor (or shift amount) of `value`, a word
/// read at `ty`: an unsigned quotient, logical shift or remainder at 32 or
/// 64 bits. Signed, narrow and 128-bit formats have none.
pub(crate) fn word_division(
    ty: MachineIntegerType,
    value: &Bitvector32Term,
) -> Option<(Division, &Bitvector32Term, &Bitvector32Term)> {
    use Bitvector32Term as T;
    use MachineIntegerType as Ty;
    let (division, operand, divisor) = match (ty, value) {
        (Ty::UInt32, T::UnsignedDivide(operand, divisor))
        | (Ty::UInt64, T::UInt64Divide(operand, divisor)) => (Division::Quotient, operand, divisor),
        (Ty::UInt32, T::LogicalShiftRight(operand, amount))
        | (Ty::UInt64, T::UInt64LogicalShiftRight(operand, amount)) => {
            (Division::ShiftRight, operand, amount)
        }
        (Ty::UInt32, T::UnsignedRemainder(operand, divisor))
        | (Ty::UInt64, T::UInt64Remainder(operand, divisor)) => {
            (Division::Remainder, operand, divisor)
        }
        _ => return None,
    };
    Some((division, operand, divisor))
}

/// Whether `ty` is one of the 32- and 64-bit formats whose conversions
/// among themselves the legacy conversion nodes (`Int64From32`,
/// `UInt32From64`, ...) spell, as `MachineIntegerType::convert_modulo_value`
/// builds them.
pub(crate) fn has_legacy_conversions(ty: MachineIntegerType) -> bool {
    matches!(word(ty), Word::Bits32 | Word::Signed64 | Word::Unsigned64) && ty.format().bits() >= 32
}

/// The 32-bit word a 32- or 64-bit value's low bits ride in: the value
/// itself at 32 bits, its `UInt32From64` narrowing at 64. `None` for a
/// narrow or 128-bit format.
pub(crate) fn low_word(ty: MachineIntegerType, value: &Bitvector32Term) -> Option<Bitvector32Term> {
    match (word(ty), ty.format().bits()) {
        (Word::Bits32, 32) => Some(value.clone()),
        (Word::Signed64 | Word::Unsigned64, _) => {
            Some(Bitvector32Term::uint32_from_64(value.clone()))
        }
        _ => None,
    }
}
