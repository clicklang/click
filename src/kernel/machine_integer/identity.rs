//! In-range identity: `to_integer(a op b) == to_integer(a) op to_integer(b)`
//! for a machine `+`, `-` or `*` of format `F` whose exact result lies in
//! `F`.
//!
//! The machine operation is the exact result reduced modulo `2^w` into
//! `F`: each operand's word is congruent to its value modulo `2^w`
//! (a narrow value's word is its canonical extension, congruent modulo
//! `2^32` and so modulo its own `2^w`), and `+`, `-` and `*` respect the
//! congruence. When the exact result lies in `F` it is the one element of
//! `F` in its residue class, so it is the machine result. The certificate
//! rule `integer_operation_identity` checks this statement for the format
//! the observation names, with the two bounds as premises.

use super::{Operation, definedness, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition};
use num_bigint::BigInt;

/// The format of the machine `+`, `-` or `*` that `observed` reads, and
/// its exact value spelled over the operands' own observations in that
/// format. `to_integer(observed) == value` is the in-range identity once
/// `value` is bounded inside the format.
pub(crate) fn mathematical(observed: &IntegerTerm) -> Option<(MachineIntegerType, IntegerTerm)> {
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    let ty = machine.ty();
    let resolved = crate::kernel::eval::read_over_write_value(machine.value());
    let (operation, left, right) =
        representation::word_operation(ty, resolved.as_ref().unwrap_or(machine.value()))?;
    let left = IntegerTerm::from_machine(ty, left.clone())?;
    let right = IntegerTerm::from_machine(ty, right.clone())?;
    Some((ty, operation.exact(left, right)))
}

/// [`mathematical`] for `+` and `-` only: the operations whose identity
/// the comparison readings and the surface's identity planner spell.
pub(crate) fn additive_mathematical(
    observed: &IntegerTerm,
) -> Option<(MachineIntegerType, IntegerTerm)> {
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    let resolved = crate::kernel::eval::read_over_write_value(machine.value());
    match representation::word_operation(
        machine.ty(),
        resolved.as_ref().unwrap_or(machine.value()),
    )? {
        (Operation::Add | Operation::Subtract, _, _) => mathematical(observed),
        (Operation::Multiply, _, _) => None,
    }
}

/// One endpoint of a format's range that the exact value of a machine
/// `+` or `-` must respect for the operation to equal that value: `exact
/// >= bound` when `lower`, else `exact <= bound`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegerOperationRangeBound {
    pub(crate) exact: IntegerTerm,
    pub(crate) bound: BigInt,
    pub(crate) lower: bool,
}

impl IntegerOperationRangeBound {
    /// The Integer facts that state this bound: its two order spellings
    /// and, for an operation with an overflow test, the definedness fact
    /// each of them reads (`definedness::definedness_of_integer_bound`).
    pub(crate) fn stating_facts(&self) -> Vec<Proposition> {
        let bound = IntegerTerm::constant(self.bound.clone());
        let forms = if self.lower {
            [
                ConditionTerm::integer_greater_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_less_equal(bound, self.exact.clone()),
            ]
        } else {
            [
                ConditionTerm::integer_less_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_greater_equal(bound, self.exact.clone()),
            ]
        };
        let mut facts = forms
            .into_iter()
            .map(|form| Proposition::ConditionIs(form, true))
            .collect::<Vec<_>>();
        // 0 <= (x - y) is exactly y <= x. Retain the native spelling
        // when both observations have the same format, so a direct machine
        // bound can certify subtraction without a difference-graph walk.
        if self.lower
            && self.bound == BigInt::from(0)
            && let IntegerTerm::Subtract(left, right) = &self.exact
            && let (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) =
                (left.as_ref(), right.as_ref())
            && left.ty() == right.ty()
        {
            facts.push(Proposition::ConditionIs(
                ConditionTerm::machine_compare(
                    left.ty(),
                    crate::kernel::CompareRelation::LessEqual,
                    right.value().clone(),
                    left.value().clone(),
                ),
                true,
            ));
        }
        if let Some(defined) = facts
            .iter()
            .find_map(definedness::definedness_of_integer_bound)
        {
            facts.push(defined);
        }
        facts
    }
}

/// The exact observation of the machine `+` or `-` in `ty` whose
/// mathematical value ([`mathematical`]) is `exact`, an Integer sum or
/// difference of observations and constants, with the range bounds the
/// operation must respect to equal it. A bound the operands' own ranges
/// already imply is not listed: `4294967295 - to_integer(b)` for `uint32`
/// `b` lies in `uint32` and needs none. The candidate is recomputed through
/// the forward map, so only an exact reading is returned.
pub(crate) fn machine_operation_of_integer_value(
    exact: &IntegerTerm,
    ty: MachineIntegerType,
) -> Option<(IntegerTerm, Vec<IntegerOperationRangeBound>)> {
    let (operation, left, right) = match Operation::of_exact(exact)? {
        found @ (Operation::Add | Operation::Subtract, _, _) => found,
        (Operation::Multiply, _, _) => return None,
    };
    // An operand's word is the one, as written or widened, whose
    // observation in `ty` gives the operand back; its range is its own
    // format's, or the constant itself.
    let operand = |side: &IntegerTerm| -> Option<(Bitvector32Term, BigInt, BigInt)> {
        match side {
            IntegerTerm::Machine(machine) => {
                let word = machine.value().clone();
                let widened = Bitvector32Term::MachineIntegerCast {
                    value: Box::new(word.clone()),
                    source: machine.ty(),
                    destination: ty,
                };
                // A value of another width is never `ty`'s word as written:
                // its word in `ty` is its widening, a node of its own.
                let as_written =
                    (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                let word = as_written.into_iter().chain([widened]).find(|word| {
                    IntegerTerm::from_machine(ty, word.clone()).as_ref() == Some(side)
                })?;
                let (low, high) = range::range(machine.ty());
                Some((word, low, high))
            }
            IntegerTerm::Constant(value) => Some((
                range::constant_word(ty, value)?,
                value.clone(),
                value.clone(),
            )),
            _ => None,
        }
    };
    let (left_word, left_low, left_high) = operand(left)?;
    let (right_word, right_low, right_high) = operand(right)?;
    let word =
        representation::operation_word(ty, operation, Box::new(left_word), Box::new(right_word))?;
    let observed = IntegerTerm::from_machine(ty, word)?;
    let (read_ty, value) = mathematical(&observed)?;
    if read_ty != ty || &value != exact {
        return None;
    }
    let (low, high) = if operation == Operation::Subtract {
        (left_low - right_high, left_high - right_low)
    } else {
        (left_low + right_low, left_high + right_high)
    };
    let (minimum, maximum) = range::range(ty);
    let mut bounds = Vec::new();
    if low < minimum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: minimum,
            lower: true,
        });
    }
    if high > maximum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: maximum,
            lower: false,
        });
    }
    Some((observed, bounds))
}
