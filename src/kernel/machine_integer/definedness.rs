//! Structural adapters between ordinary exact-result bounds and the private
//! overflow queries used by existing interval reasoning. Generated arithmetic
//! domains are ordinary propositions; these adapters never file an opaque
//! overflow fact or alter a lowered term.
//! A single bound identifies a candidate query, but only both bounds establish
//! representability. Unsigned overflow remains wrapping arithmetic.

use super::{FORMATS, Operation, range, representation};
use crate::kernel::{Bitvector32Term, ConditionTerm, IntegerTerm, MachineIntegerType, Proposition};

/// The formats whose definedness facts the kernel files, narrowest first:
/// those where C arithmetic's overflow is undefined behavior
/// (`representation::files_definedness`).
pub(crate) fn defined_formats() -> impl Iterator<Item = MachineIntegerType> {
    FORMATS
        .into_iter()
        .filter(|ty| representation::files_definedness(*ty))
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
/// ([`integer_bounds_of_definedness`]) is exactly `bound`, if any, at a
/// format whose definedness facts are filed ([`defined_formats`]). The
/// candidate is recomputed through the forward map, so only an exact
/// reading is accepted.
pub(crate) fn definedness_of_integer_bound(bound: &Proposition) -> Option<Proposition> {
    overflow_fact_of_integer_bound(bound, defined_formats())
}

/// The fact `not Overflows(F, op, a, b)`, for `F` among `formats`, whose
/// Integer bound ([`integer_bounds_of_definedness`]) is exactly `bound`,
/// if any: the converse of the equivalence, at any format.
pub(crate) fn overflow_fact_of_integer_bound(
    bound: &Proposition,
    formats: impl Iterator<Item = MachineIntegerType>,
) -> Option<Proposition> {
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
                // A value of another width is never `ty`'s word as written:
                // its word in `ty` is its widening, a node of its own.
                let as_written =
                    (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                as_written
                    .into_iter()
                    .chain([widened])
                    .find(|word| IntegerTerm::from_machine(ty, word.clone()).as_ref() == Some(side))
            }
            IntegerTerm::Constant(value) => range::constant_word(ty, value),
            _ => None,
        }
    };
    if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
        return None;
    }
    formats
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
                .iter()
                .any(|expected| same_integer_bound(expected, bound))
                .then_some(fact)
        })
}

/// The two order spellings of an ordinary bound are the same proposition.
/// This is comparison matching, never a change to either stored term.
fn same_integer_bound(left: &Proposition, right: &Proposition) -> bool {
    left == right
        || matches!((left, right),
        (Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true),
         Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(c, d), true)) |
        (Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(a, b), true),
         Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(c, d), true))
        if a == d && b == c)
}

/// Read one explicitly supplied ordinary range conjunction as an arithmetic
/// query. This is a structural adapter for existing interval certificates;
/// it neither adds an overflow fact nor searches the context for bounds.
pub(crate) fn ordinary_arithmetic_guard(proposition: &Proposition) -> Option<ConditionTerm> {
    let Proposition::And(first, second) = proposition else {
        return None;
    };
    let fact = definedness_of_integer_bound(first)?;
    let bounds = integer_bounds_of_definedness(&fact);
    let [upper, lower] = bounds.as_slice() else {
        return None;
    };
    if !(same_integer_bound(first, upper) && same_integer_bound(second, lower)
        || same_integer_bound(first, lower) && same_integer_bound(second, upper))
    {
        return None;
    }
    let Proposition::ConditionIs(condition, false) = fact else {
        return None;
    };
    Some(condition)
}

/// Private input form for the existing interval proof rules. Stored facts,
/// obligations and certificate results keep the ordinary propositions. This
/// adapter reads only the explicit proposition, never the ambient context.
pub(crate) fn interval_query_form(proposition: &Proposition) -> Option<Proposition> {
    if let Some(condition) = ordinary_arithmetic_guard(proposition) {
        return Some(Proposition::ConditionIs(condition, false));
    }
    if let Proposition::And(left, right) = proposition {
        let a = interval_query_form(left);
        let b = interval_query_form(right);
        if a.is_some() || b.is_some() {
            return Some(Proposition::And(
                Box::new(a.unwrap_or_else(|| *left.clone())),
                Box::new(b.unwrap_or_else(|| *right.clone())),
            ));
        }
    }
    None
}
