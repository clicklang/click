//! The one map between a format and the term nodes that spell it today.
//!
//! The term arena records no width (`docs/internals/kernel.md`, "Important
//! types"): a 32- or 64-bit operation is a `Binary` node carrying its
//! format, and values of 8 and 16 bits ride in the 32-bit word as
//! their sign or zero extension. Rules ask this module for the node of an
//! operation, comparison or overflow test at a format, or for the format
//! and operation a node spells, and never match on a width themselves.
//!
//! Conditions carry their format (`ConditionTerm::Compare` and
//! `ConditionTerm::Overflows`), so a comparison or overflow test exists at
//! every format. Where a format has no operator node the answer is `None`,
//! and the rule is unavailable there: there are no 128-bit operators. That
//! is the representation gap `design/machine-integers.md` Stage 3 removes;
//! the test matrix names each one.

use super::{Operation, Relation};
use crate::kernel::MachineBinaryOp;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{Bitvector32Term, ConditionTerm, MachineIntegerType};
use crate::kernel::{CompareRelation, OverflowOperation};

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
    let (left, right) = if word(ty) == Word::Bits32 {
        (
            Box::new(left.constant_word32()),
            Box::new(right.constant_word32()),
        )
    } else {
        (left, right)
    };
    Some(match (word(ty), operation) {
        (Word::Bits32, Operation::Add) => binary_node!(Int32, Add, left, right),
        (Word::Bits32, Operation::Subtract) => binary_node!(Int32, Subtract, left, right),
        (Word::Bits32, Operation::Multiply) => binary_node!(Int32, Multiply, left, right),
        (Word::Signed64 | Word::Unsigned64, operation) => T::Binary {
            format: ty,
            op: machine_binary_op_of(operation),
            left,
            right,
        },
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
        (Word::Bits32, binary_term!(Int32, Add, left, right)) => (Operation::Add, left, right),
        (Word::Bits32, binary_term!(Int32, Subtract, left, right)) => {
            (Operation::Subtract, left, right)
        }
        (Word::Bits32, binary_term!(Int32, Multiply, left, right)) => {
            (Operation::Multiply, left, right)
        }
        (
            Word::Signed64 | Word::Unsigned64,
            T::Binary {
                format,
                op,
                left,
                right,
            },
        ) if *format == ty => (operation_of_machine_binary_op(*op)?, left, right),
        _ => return None,
    };
    Some((operation, left, right))
}

/// The format-carrying operator of a ring operation.
fn machine_binary_op_of(operation: Operation) -> MachineBinaryOp {
    match operation {
        Operation::Add => MachineBinaryOp::Add,
        Operation::Subtract => MachineBinaryOp::Subtract,
        Operation::Multiply => MachineBinaryOp::Multiply,
    }
}

/// The ring operation a format-carrying operator is, if any.
fn operation_of_machine_binary_op(op: MachineBinaryOp) -> Option<Operation> {
    match op {
        MachineBinaryOp::Add => Some(Operation::Add),
        MachineBinaryOp::Subtract => Some(Operation::Subtract),
        MachineBinaryOp::Multiply => Some(Operation::Multiply),
        _ => None,
    }
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
/// filed at (`!=` is a false equality), built by the folding constructor
/// (`ConditionTerm::machine_compare`). A narrow value's word is its
/// canonical extension, which the signed 32-bit order compares exactly, as
/// C's promotion to `int` does.
pub(crate) fn comparison(
    ty: MachineIntegerType,
    relation: Relation,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Option<(ConditionTerm, bool)> {
    let compare = match relation {
        Relation::Less => CompareRelation::LessThan,
        Relation::LessEqual => CompareRelation::LessEqual,
        Relation::Equal | Relation::NotEqual => CompareRelation::Equal,
    };
    Some((
        ConditionTerm::machine_compare(ty, compare, left, right),
        relation != Relation::NotEqual,
    ))
}

/// Whether an Integer comparison of exact observations of `ty` is spelled
/// as its native comparison. Every format has the native node
/// ([`comparison`]) and reads back from it; a 128-bit comparison keeps its
/// Integer form, because the kernel's order reasoning (the difference
/// graph, interval bounds) has no 128-bit nodes and decides it as Integers.
pub(crate) fn spells_comparison_natively(ty: MachineIntegerType) -> bool {
    word(ty) != Word::Bits128
}

/// The operands of a native comparison and the formats whose exact reading
/// it may be, most specific first. A narrow value reads through the `int32`
/// reading, which `IntegerTerm::from_machine` normalizes to the narrow
/// observation. An equality reads no sign, so it reads at both formats of
/// its width.
pub(crate) fn comparison_readings(
    condition: &ConditionTerm,
) -> Option<(
    &Bitvector32Term,
    &Bitvector32Term,
    &'static [MachineIntegerType],
)> {
    use MachineIntegerType as Ty;
    let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let equality = *relation == CompareRelation::Equal;
    let types: &'static [MachineIntegerType] = match (format, equality) {
        (Ty::Int32, false) => &[Ty::Int32],
        (Ty::Int32 | Ty::UInt32, true) => &[Ty::Int32, Ty::UInt32],
        (Ty::UInt32, false) => &[Ty::UInt32],
        (Ty::Int64, false) => &[Ty::Int64],
        (Ty::Int64, true) => &[Ty::Int64, Ty::UInt64],
        (Ty::UInt64, false) => &[Ty::UInt64],
        (Ty::Int128, false) => &[Ty::Int128],
        (Ty::Int128, true) => &[Ty::Int128, Ty::UInt128],
        (Ty::UInt128, false) => &[Ty::UInt128],
        _ => return None,
    };
    Some((left, right, types))
}

/// Whether `ty` has an overflow test for `+`, `-` and `*`
/// ([`overflow_condition`]): every format has one, the `Overflows` node.
pub(crate) fn has_overflow_test(_ty: MachineIntegerType) -> bool {
    true
}

/// Whether C arithmetic at `ty` can overflow its own range, so that its
/// overflow is undefined behavior a definedness fact is filed for: the
/// signed formats C computes at, `int32` and `int64`. Narrow operands are
/// promoted to `int` first, 128-bit values have no arithmetic, and unsigned
/// arithmetic wraps, which is defined (`design/machine-integers.md`,
/// "Decisions", 2026-10-24).
pub(crate) fn files_definedness(ty: MachineIntegerType) -> bool {
    matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::Int64)
}

fn overflow_operation_of(operation: Operation) -> OverflowOperation {
    match operation {
        Operation::Add => OverflowOperation::Add,
        Operation::Subtract => OverflowOperation::Subtract,
        Operation::Multiply => OverflowOperation::Multiply,
    }
}

/// The overflow test of `left op right` at `ty`, as the unsimplified node
/// a definedness fact files. `None` where `ty` has no overflow test
/// ([`has_overflow_test`]).
pub(crate) fn overflow_condition(
    ty: MachineIntegerType,
    operation: Operation,
    left: Box<Bitvector32Term>,
    right: Box<Bitvector32Term>,
) -> Option<ConditionTerm> {
    has_overflow_test(ty).then(|| ConditionTerm::Overflows {
        format: ty,
        op: overflow_operation_of(operation),
        left,
        right,
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
    let ConditionTerm::Overflows {
        format,
        op,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let operation = match op {
        OverflowOperation::Add => Operation::Add,
        OverflowOperation::Subtract => Operation::Subtract,
        OverflowOperation::Multiply => Operation::Multiply,
        OverflowOperation::Divide | OverflowOperation::ShiftLeft => return None,
    };
    has_overflow_test(*format).then_some((*format, operation, &**left, &**right))
}

/// A truncating quotient, floor right shift or remainder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Division {
    /// `x / d`, truncated toward zero.
    Quotient,
    /// `x >> k`: the floor of `x / 2^k`, logical for an unsigned format and
    /// arithmetic for a signed one.
    ShiftRight,
    /// `x % d`, with the sign of `x`.
    Remainder,
}

/// The division, operand and divisor (or shift amount) of `value`, a word
/// read at `ty`. The operation's signedness is the format's: an unsigned
/// format's quotient is `UnsignedDivide`, a signed one's `Divide`. Narrow
/// and 128-bit formats have none.
pub(crate) fn word_division(
    ty: MachineIntegerType,
    value: &Bitvector32Term,
) -> Option<(Division, &Bitvector32Term, &Bitvector32Term)> {
    use Bitvector32Term as T;
    use MachineIntegerType as Ty;
    let (division, operand, divisor) = match (ty, value) {
        (Ty::UInt32, binary_term!(UInt32, Divide, operand, divisor))
        | (
            Ty::UInt64,
            T::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Divide,
                left: operand,
                right: divisor,
            },
        )
        | (Ty::Int32, binary_term!(Int32, Divide, operand, divisor))
        | (
            Ty::Int64,
            T::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Divide,
                left: operand,
                right: divisor,
            },
        ) => (Division::Quotient, operand, divisor),
        (Ty::UInt32, binary_term!(UInt32, ShiftRight, operand, amount))
        | (
            Ty::UInt64,
            T::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftRight,
                left: operand,
                right: amount,
            },
        )
        | (Ty::Int32, binary_term!(Int32, ShiftRight, operand, amount))
        | (
            Ty::Int64,
            T::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::ShiftRight,
                left: operand,
                right: amount,
            },
        ) => (Division::ShiftRight, operand, amount),
        (Ty::UInt32, binary_term!(UInt32, Remainder, operand, divisor))
        | (
            Ty::UInt64,
            T::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: operand,
                right: divisor,
            },
        )
        | (Ty::Int32, binary_term!(Int32, Remainder, operand, divisor))
        | (
            Ty::Int64,
            T::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Remainder,
                left: operand,
                right: divisor,
            },
        ) => (Division::Remainder, operand, divisor),
        _ => return None,
    };
    Some((division, operand, divisor))
}

/// Whether `ty` is one of the 32- and 64-bit formats whose conversions
/// among themselves the legacy conversion nodes (`Int64From32`,
/// `UInt32From64`, ...) spell, as `conversion::convert_value`
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

/// The mask and, for a signed format, the sign bit that spell an 8- or
/// 16-bit format's canonical carrier of a word's low bits (rule K7,
/// [`narrow_cast_word`]): `(2^w - 1, None)` unsigned, `(2^w - 1, Some(2^(w-1)))`
/// signed. `None` for a format of 32 bits or more.
pub(crate) fn narrow_carrier_mask(ty: MachineIntegerType) -> Option<(u32, Option<u32>)> {
    let format = ty.format();
    let bits = format.bits();
    if bits >= 32 {
        return None;
    }
    let mask = (1u32 << bits) - 1;
    Some((mask, format.is_signed().then_some(1u32 << (bits - 1))))
}

/// Rule K7 (`design/machine-integers.md`, Decisions, 2026-10-26): the
/// 32-bit word of `Cast(source -> destination, value)` into an 8- or 16-bit
/// format, from a source of at most 64 bits. With `w` the operand's word
/// (`value` itself up to 32 bits, its low word `UInt32From64(value)` at 64),
/// `m = 2^bits - 1` and `s = 2^(bits - 1)`:
///
/// - unsigned destination: `w & m`;
/// - signed destination: `((w & m) ^ s) - s`.
///
/// Soundness: the cast denotes `n mod 2^bits` read in the destination, `n`
/// the operand's value, and by the narrow-value invariant
/// (`docs/internals/kernel.md`, "One meaning for a narrow value") its word
/// is the zero or sign extension of those low bits. The operand's word, or
/// low word, is `n mod 2^32`, whose low `bits` bits are `n mod 2^bits`. The
/// mask zero-extends them; for `b` those bits, `(b ^ s) - s` is `b` when
/// `b < s` and `b - 2^bits` otherwise, with no 32-bit wrap, which is their
/// sign extension. `None` for any other conversion.
///
/// The e-graph interns this word from the operand's class
/// (`TermClasses::narrow_cast_node`); the matrix checks it value by value.
#[cfg(test)]
pub(crate) fn narrow_cast_word(
    source: MachineIntegerType,
    destination: MachineIntegerType,
    value: Bitvector32Term,
) -> Option<Bitvector32Term> {
    let (mask, sign) = narrow_carrier_mask(destination)?;
    let word = match source.format().bits() {
        8 | 16 | 32 => value,
        64 => Bitvector32Term::uint32_from_64(value),
        _ => return None,
    };
    let low = Bitvector32Term::bitwise_and(word, Bitvector32Term::Constant(mask));
    Some(match sign {
        None => low,
        Some(sign) => Bitvector32Term::subtract(
            Bitvector32Term::bitwise_xor(low, Bitvector32Term::Constant(sign)),
            Bitvector32Term::Constant(sign),
        ),
    })
}
