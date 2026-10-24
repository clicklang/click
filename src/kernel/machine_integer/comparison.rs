//! Exact comparison: `to_integer(a) R to_integer(b)` holds exactly when the
//! native comparison of `a` and `b` at their format does. `to_integer` is
//! injective and order-preserving on every format, so the two comparisons
//! have the same truth.

use super::{Relation, identity, range, representation};
use crate::kernel::{
    Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition, SharedIntegerTerm,
};

/// An Integer comparison as `left REL right` with its truth folded in:
/// `>`/`>=` swap their operands, and a false comparison is negated.
fn integer_relation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Relation, &SharedIntegerTerm, &SharedIntegerTerm)> {
    let (relation, left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right) => (Relation::Less, left, right),
        ConditionTerm::IntegerLessEqual(left, right) => (Relation::LessEqual, left, right),
        ConditionTerm::IntegerGreaterThan(left, right) => (Relation::Less, right, left),
        ConditionTerm::IntegerGreaterEqual(left, right) => (Relation::LessEqual, right, left),
        ConditionTerm::IntegerEqual(left, right) => (Relation::Equal, left, right),
        ConditionTerm::IntegerNotEqual(left, right) => (Relation::NotEqual, left, right),
        _ => return None,
    };
    Some(match (relation, value) {
        (relation, true) => (relation, left, right),
        // not (l < r) is r <= l; not (l <= r) is r < l.
        (Relation::Less, false) => (Relation::LessEqual, right, left),
        (Relation::LessEqual, false) => (Relation::Less, right, left),
        (Relation::Equal, false) => (Relation::NotEqual, left, right),
        (Relation::NotEqual, false) => (Relation::Equal, left, right),
    })
}

/// The native machine comparison equivalent to the Integer comparison
/// `condition` with truth `value`, when both sides observe one machine
/// format exactly: `to_integer(x)` against `to_integer(y)` of the same
/// format, or against a constant that format represents. A constant outside
/// the format's range makes the Integer comparison decided by the range
/// alone; nothing is returned for it, nor for a format with no native
/// comparison (`representation::comparison`).
pub(crate) fn native_comparison_of_integer_observation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    let (relation, left, right) = integer_relation(condition, value)?;
    let ty = match (&**left, &**right) {
        (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) if left.ty() == right.ty() => {
            left.ty()
        }
        (IntegerTerm::Machine(machine), IntegerTerm::Constant(_))
        | (IntegerTerm::Constant(_), IntegerTerm::Machine(machine)) => machine.ty(),
        _ => return None,
    };
    // A narrow value's word is the canonical carrier of its format, its
    // zero or sign extension, which the signed 32-bit order compares
    // exactly, as C's promotion to `int` does. The native form is taken only
    // where its Integer reading, an `int32` observation of the word, is this
    // same narrow observation again (`IntegerTerm::from_machine`
    // normalizes a narrow load or conversion so), keeping one spelling per
    // value. A binder's word does not name its format, so a comparison of
    // a narrow binder keeps its Integer form.
    let narrow = ty.format().bits() < 32;
    let carrier = |side: &IntegerTerm| -> Option<Bitvector32Term> {
        match side {
            IntegerTerm::Machine(machine)
                if narrow
                    && IntegerTerm::from_machine(
                        MachineIntegerType::Int32,
                        machine.value().clone(),
                    )
                    .as_ref()
                        != Some(side) =>
            {
                None
            }
            IntegerTerm::Machine(machine) => Some(machine.value().clone()),
            IntegerTerm::Constant(constant) => range::constant_word(ty, constant),
            _ => None,
        }
    };
    let left = carrier(left)?;
    let right = carrier(right)?;
    representation::comparison(ty, relation, left, right)
}

/// The native comparison an Integer comparison holds exactly when, read
/// through in-range machine operations: each side that is the exact value
/// of a machine `+` or `-` of observations of one format is replaced by
/// that operation's observation
/// (`identity::machine_operation_of_integer_value`), and the result is read
/// as [`native_comparison_of_integer_observation`] reads it.
/// `to_integer(a) <= 4294967295 - to_integer(b)` on `uint32` reads as
/// `a <= 4294967295u32 - b`. The returned bounds are what each replaced
/// operation needs to equal its exact value; the reading holds only with
/// them. A comparison with no operation side, or whose native form folds
/// to a constant, has no such reading. At most one candidate format per
/// observation the two sides name is tried; nothing else is visited.
pub(crate) fn native_comparison_through_integer_operations(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(
    ConditionTerm,
    bool,
    Vec<identity::IntegerOperationRangeBound>,
)> {
    let (left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => (&**left, &**right),
        _ => return None,
    };
    let operation =
        |side: &IntegerTerm| matches!(side, IntegerTerm::Add(..) | IntegerTerm::Subtract(..));
    if !operation(left) && !operation(right) {
        return None;
    }
    // The machine formats the sides observe, directly or as operands.
    let mut types = Vec::new();
    for side in [left, right] {
        let operands = match side {
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) => vec![&**a, &**b],
            other => vec![other],
        };
        for operand in operands {
            if let IntegerTerm::Machine(machine) = operand
                && !types.contains(&machine.ty())
            {
                types.push(machine.ty());
            }
        }
    }
    types.into_iter().find_map(|ty| {
        let mut bounds = Vec::new();
        let mut read = |side: &IntegerTerm| -> Option<IntegerTerm> {
            if !operation(side) {
                return Some(side.clone());
            }
            let (observed, needed) = identity::machine_operation_of_integer_value(side, ty)?;
            bounds.extend(needed);
            Some(observed)
        };
        let (left, right) = (read(left)?, read(right)?);
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let read = match condition {
            ConditionTerm::IntegerLessThan(..) => ConditionTerm::IntegerLessThan(left, right),
            ConditionTerm::IntegerLessEqual(..) => ConditionTerm::IntegerLessEqual(left, right),
            ConditionTerm::IntegerGreaterThan(..) => ConditionTerm::IntegerGreaterThan(left, right),
            ConditionTerm::IntegerGreaterEqual(..) => {
                ConditionTerm::IntegerGreaterEqual(left, right)
            }
            ConditionTerm::IntegerEqual(..) => ConditionTerm::IntegerEqual(left, right),
            _ => ConditionTerm::IntegerNotEqual(left, right),
        };
        match native_comparison_of_integer_observation(&read, value)? {
            (ConditionTerm::Constant(_), _) => None,
            (native, truth) => Some((native, truth, bounds)),
        }
    })
}

/// The Integer comparisons of exact observations whose native comparison
/// ([`native_comparison_of_integer_observation`]) is exactly `proposition`,
/// a native comparison fact: `1u32 <= x` gives `1 <= to_integer(x)`. Each
/// candidate is recomputed through the forward map, so only exact
/// converses, up to the fact's equivalent order spellings, are returned. A
/// 32-bit word comparison may read as `int32` and, when its operands carry
/// the unsigned sign-bit encoding, as `uint32`
/// (`representation::comparison_readings`).
pub(crate) fn integer_observations_of_native_comparison(
    proposition: &Proposition,
) -> Vec<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return Vec::new();
    };
    let Some((left, right, types)) = representation::comparison_readings(condition) else {
        return Vec::new();
    };
    // A native order has four spellings (`a >= 1` is `1 <= a`, and a false
    // `0 < x` is `x <= 0`) in every order family; the forward map produces
    // one, so compare against all of them.
    let spellings = crate::kernel::proof::fact_reasoning::order_claim_forms(proposition);
    let mut lifted = Vec::new();
    for &ty in types {
        let (Some(left), Some(right)) = (
            representation::order_operand(ty, condition, left),
            representation::order_operand(ty, condition, right),
        ) else {
            continue;
        };
        let (Some(left), Some(right)) = (
            IntegerTerm::from_machine(ty, left),
            IntegerTerm::from_machine(ty, right),
        ) else {
            continue;
        };
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let candidates = [
            ConditionTerm::IntegerLessEqual(left.clone(), right.clone()),
            ConditionTerm::IntegerLessThan(left.clone(), right.clone()),
            ConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
            ConditionTerm::IntegerLessThan(right.clone(), left.clone()),
            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
        ];
        for candidate in candidates {
            let truth = if matches!(candidate, ConditionTerm::IntegerEqual(..)) {
                *value
            } else {
                true
            };
            if native_comparison_of_integer_observation(&candidate, truth).is_some_and(
                |(native, native_truth)| {
                    let native = Proposition::ConditionIs(native, native_truth);
                    &native == proposition || spellings.contains(&native)
                },
            ) {
                lifted.push(Proposition::ConditionIs(candidate, truth));
                break;
            }
        }
    }
    lifted
}
