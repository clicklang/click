//! Definedness: `not overflows(F, op, a, b)` holds exactly when the exact
//! result `to_integer(a) op to_integer(b)` lies in `F`. That is the
//! definition of each overflow test: it is true exactly when the exact
//! result is not representable in the operands' format.
//!
//! Only `int32` and `int64` have an overflow test today
//! (`representation::overflow_condition`); an unsigned, narrow or 128-bit
//! definedness fact has no condition to be filed as, which is the
//! representation gap `design/machine-integers.md` Stage 2 closes with
//! `Overflows { format, op, left, right }`.

use super::{FORMATS, Operation, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition};

/// The formats with an overflow test for `+`, `-` and `*`, narrowest first.
pub(crate) fn defined_formats() -> impl Iterator<Item = MachineIntegerType> {
    FORMATS.into_iter().filter(|ty| has_overflow_test(*ty))
}

/// Whether `ty` has an overflow test, so that a definedness fact can be
/// stated at it.
pub(crate) fn has_overflow_test(ty: MachineIntegerType) -> bool {
    representation::has_overflow_test(ty)
}

/// The two Integer bounds a definedness fact is exactly equivalent to:
/// `defined(a + b)` on `int32` holds exactly when
/// `to_integer(a) + to_integer(b) <= 2147483647` and
/// `to_integer(a) + to_integer(b) >= -2147483648`, and likewise for `-`
/// and `*` and for every format with an overflow test. A refutation may
/// read the definedness fact as these bounds
/// ([`definedness_of_integer_bound`] checks a listed one).
pub(crate) fn integer_bounds_of_definedness(proposition: &Proposition) -> Vec<Proposition> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return Vec::new();
    };
    let Some((ty, operation, left, right)) = representation::overflow_operation(condition) else {
        return Vec::new();
    };
    let (Some(left), Some(right)) = (
        IntegerTerm::from_machine(ty, left.clone()),
        IntegerTerm::from_machine(ty, right.clone()),
    ) else {
        return Vec::new();
    };
    let (minimum, maximum) = range::range(ty);
    let exact = operation.exact(left, right);
    vec![
        Proposition::ConditionIs(
            ConditionTerm::integer_less_equal(exact.clone(), IntegerTerm::constant(maximum)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::integer_greater_equal(exact, IntegerTerm::constant(minimum)),
            true,
        ),
    ]
}

/// The definedness fact whose Integer bound
/// ([`integer_bounds_of_definedness`]) is exactly `bound`, if any. The
/// candidate is recomputed through the forward map, so only an exact
/// reading is accepted.
pub(crate) fn definedness_of_integer_bound(bound: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(first, second)
        | ConditionTerm::IntegerGreaterEqual(first, second),
        true,
    ) = bound
    else {
        return None;
    };
    // The comparison constructors may put the constant on either side.
    let exact = if Operation::of_exact(first).is_some() {
        first
    } else {
        second
    };
    let (_, left, right) = Operation::of_exact(exact)?;
    // An operand is an observation in the operation's format, or a
    // constant, which the forward map produces for a literal operand such
    // as `x + 1`. An `int32` observation of a narrow load or of a widened
    // narrow value reads as the narrow format's
    // (`IntegerTerm::from_machine`), so an operand's word is the one, as
    // written or widened, whose observation in the format gives the
    // operand back.
    let carrier = |ty: MachineIntegerType, side: &IntegerTerm| -> Option<Bitvector32Term> {
        match side {
            IntegerTerm::Machine(machine) => {
                let word = machine.value().clone();
                let widened = Bitvector32Term::MachineIntegerCast {
                    value: Box::new(word.clone()),
                    source: machine.ty(),
                    destination: ty,
                };
                [word, widened]
                    .into_iter()
                    .find(|word| IntegerTerm::from_machine(ty, word.clone()).as_ref() == Some(side))
            }
            IntegerTerm::Constant(value) => range::constant_word(ty, value),
            _ => None,
        }
    };
    if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
        return None;
    }
    defined_formats()
        .filter_map(|ty| {
            let (a, b) = (Box::new(carrier(ty, left)?), Box::new(carrier(ty, right)?));
            Some(Operation::ALL.map(|operation| {
                representation::overflow_condition(ty, operation, a.clone(), b.clone())
            }))
        })
        .flatten()
        .flatten()
        .find_map(|condition| {
            let fact = Proposition::ConditionIs(condition, false);
            integer_bounds_of_definedness(&fact)
                .contains(bound)
                .then_some(fact)
        })
}
