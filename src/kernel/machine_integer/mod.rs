//! The correspondences between machine-integer facts and `Integer` facts,
//! each stated once over a format (`design/machine-integers.md`, "Rules
//! stated once over a format").
//!
//! A format is a width and a signedness, named by `MachineIntegerType`
//! (`MachineIntegerType::format`). Every rule here takes the format as a
//! parameter, and no caller lists the widths a rule supports:
//!
//! - [`comparison`]: exact comparison. `to_integer(a) R to_integer(b)`
//!   holds exactly when the native comparison of `a` and `b` at their
//!   format does, and its converse reading.
//! - [`range`]: `min(F) <= to_integer(v) <= max(F)`, and the word that
//!   spells a constant of `F`.
//! - [`identity`]: in-range identity. `to_integer(a op b) == to_integer(a)
//!   op to_integer(b)` for `+ - *` when the exact result lies in `F`.
//! - [`bounds`]: the bounds a quotient, remainder or right shift by a
//!   constant puts on its operand.
//! - [`definedness`]: `not overflows(F, op, a, b)` holds exactly when the
//!   exact result lies in `F`.
//! - [`modular`]: an `Integer` equality over `+ - *` of observations of one
//!   format implies the word equality modulo `2^w`.
//! - [`conversion`]: a cast preserves its operand's value inside the
//!   destination; widening needs no premise, narrowing needs the range.
//!
//! The term representation still spells each width with its own nodes
//! (`Add` at 32 bits, `Int64Add` at 64, no operators at 128). The one place
//! that maps a format to those nodes, and back, is [`representation`]. A
//! rule that has no node at some format is unavailable there, and the test
//! matrix (`matrix_tests.rs`) records each such format as a named
//! representation gap, so a format a rule silently misses fails a test.

pub(crate) mod bounds;
pub(crate) mod comparison;
pub(crate) mod conversion;
pub(crate) mod definedness;
pub(crate) mod identity;
pub(crate) mod modular;
pub(crate) mod range;
pub(crate) mod representation;

#[cfg(test)]
mod matrix_tests;

use crate::kernel::{IntegerTerm, MachineIntegerType};

/// Every machine-integer format, narrowest first, signed before unsigned.
/// The test matrix runs every rule at each of them.
pub(crate) const FORMATS: [MachineIntegerType; 10] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
    MachineIntegerType::Int128,
    MachineIntegerType::UInt128,
];

/// A comparison, as `left REL right`. `>` and `>=` are `<` and `<=` with
/// the operands swapped.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum Relation {
    Less,
    LessEqual,
    Equal,
    NotEqual,
}

impl Relation {
    #[cfg(test)]
    pub(crate) const ALL: [Self; 4] = [Self::Less, Self::LessEqual, Self::Equal, Self::NotEqual];
}

/// A ring operation whose machine result is its exact result reduced
/// modulo `2^w` into the format.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) enum Operation {
    Add,
    Subtract,
    Multiply,
}

impl Operation {
    pub(crate) const ALL: [Self; 3] = [Self::Add, Self::Subtract, Self::Multiply];

    /// The exact `Integer` result of the operation on `left` and `right`.
    pub(crate) fn exact(self, left: IntegerTerm, right: IntegerTerm) -> IntegerTerm {
        match self {
            Self::Add => IntegerTerm::add(left, right),
            Self::Subtract => IntegerTerm::subtract(left, right),
            Self::Multiply => IntegerTerm::multiply(left, right),
        }
    }

    /// The operation an exact `Integer` term applies at its root, with its
    /// operands, as written (no simplification).
    pub(crate) fn of_exact(term: &IntegerTerm) -> Option<(Self, &IntegerTerm, &IntegerTerm)> {
        match term {
            IntegerTerm::Add(left, right) => Some((Self::Add, &**left, &**right)),
            IntegerTerm::Subtract(left, right) => Some((Self::Subtract, &**left, &**right)),
            IntegerTerm::Multiply(left, right) => Some((Self::Multiply, &**left, &**right)),
            _ => None,
        }
    }
}
