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
/// alone; nothing is returned for it, nor for a format whose Integer
/// comparisons keep their Integer spelling
/// (`representation::spells_comparison_natively`).
pub(crate) fn native_comparison_of_integer_observation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    // Numeric evaluation belongs in the checking comparison form. Surface
    // lowering uses the structural reading below, retaining arithmetic.
    // An observation is read through its value relations (rule W):
    // `to_integer(d as int128) != 0` is `d != 0`.
    let operand = |term: &SharedIntegerTerm| -> Option<SharedIntegerTerm> {
        let read = term.value_read();
        if !std::ptr::eq(read, term.as_ref()) {
            return Some(read.clone().into());
        }
        if !term.is_literal_arithmetic() || term.as_const().is_some() {
            return Some(term.clone());
        }
        crate::kernel::proof::integer_arithmetic::literal_integer_value(term)
            .map(|value| IntegerTerm::constant(value).into())
    };
    let condition = match condition {
        ConditionTerm::IntegerLessThan(left, right) => {
            ConditionTerm::IntegerLessThan(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            ConditionTerm::IntegerLessEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            ConditionTerm::IntegerGreaterThan(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            ConditionTerm::IntegerGreaterEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            ConditionTerm::IntegerEqual(operand(left)?, operand(right)?)
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            ConditionTerm::IntegerNotEqual(operand(left)?, operand(right)?)
        }
        _ => return None,
    };
    structural_native_comparison_of_integer_observation(&condition, value)
}

pub(crate) fn structural_native_comparison_of_integer_observation(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(ConditionTerm, bool)> {
    // A 128-bit comparison has a native node, but the kernel's order
    // reasoning (the difference graph, interval bounds) works on its
    // Integer form, so an Integer comparison of 128-bit observations keeps
    // that spelling (`representation::spells_comparison_natively`).
    let spelled_natively = |side: &IntegerTerm| match side {
        IntegerTerm::Machine(machine) => representation::spells_comparison_natively(machine.ty()),
        _ => true,
    };
    if let ConditionTerm::IntegerLessThan(left, right)
    | ConditionTerm::IntegerLessEqual(left, right)
    | ConditionTerm::IntegerGreaterThan(left, right)
    | ConditionTerm::IntegerGreaterEqual(left, right)
    | ConditionTerm::IntegerEqual(left, right)
    | ConditionTerm::IntegerNotEqual(left, right) = condition
        && !(spelled_natively(left) && spelled_natively(right))
    {
        return None;
    }
    native_comparison_at_format(condition, value)
}

/// [`native_comparison_of_integer_observation`] at every format, whatever
/// its spelling: the forward map the converse reading checks against.
fn native_comparison_at_format(
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
    // An 8- or 16-bit observation is a native value of its format, compared
    // natively at it; a constant is that format's constant. An observation
    // whose operand is a word of another width (the byte of a 32-bit sum)
    // has no native comparison: its root width, read in O(1), decides.
    let narrow = ty.format().bits() < 32;
    let carrier = |side: &IntegerTerm| -> Option<Bitvector32Term> {
        match side {
            IntegerTerm::Machine(machine)
                if narrow
                    && crate::kernel::root_width(machine.value()).is_some_and(|width| {
                        width != crate::kernel::CarrierWidth::of_machine_type(ty)
                    }) =>
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
        | ConditionTerm::IntegerNotEqual(left, right) => {
            // Each side is read through its observations' value relations
            // (rule W), so `to_integer(x as uint32) + 1` is an operation on
            // `x`'s own format. Both readings are cached on the sides.
            (&**left.read_through_ref(), &**right.read_through_ref())
        }
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

/// The Integer readings of a native comparison fact
/// ([`integer_observations_of_native_comparison`]), and of a promoted
/// comparison of widenings ([`integer_comparisons_of_widenings`]). A native
/// 8- or 16-bit comparison is the same fact as the `int32` comparison of
/// its operands' widenings (rule K8, [`narrow_comparison_as_int32`]), so it
/// has that comparison's readings.
pub(crate) fn integer_readings_with_promotions(proposition: &Proposition) -> Vec<Proposition> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        let promoted = narrow_comparison_as_int32(condition);
        let widened =
            integer_comparisons_of_widenings(promoted.as_ref().unwrap_or(condition), *value);
        if !widened.is_empty() {
            return widened;
        }
    }
    integer_observations_of_native_comparison(proposition)
}

/// A native 8- or 16-bit comparison as the signed `int32` comparison of its
/// operands' widenings, which hold the same values (rule K8): `a <=_u8 b`
/// holds exactly when `widen(a) <= widen(b)` does. Order and interval
/// reasoning keeps its facts on 32-bit terms; this is its one bridge to a
/// native narrow fact, filed beside it and consulted for a native goal. The
/// comparison is built by the folding constructor, so it is the same term a
/// promoted comparison of the widenings is. `None` for any other condition.
/// One match on the root and two widenings.
pub(crate) fn narrow_comparison_as_int32(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if format.format().bits() >= 32 {
        return None;
    }
    let widen = |term: &Bitvector32Term| {
        super::conversion::convert_term(*format, MachineIntegerType::Int32, term.clone())
    };
    Some(ConditionTerm::machine_compare(
        MachineIntegerType::Int32,
        *relation,
        widen(left),
        widen(right),
    ))
}

/// The `int32` spelling a native 8- or 16-bit comparison fact is also filed
/// under by the 32-bit indexes (order bounds, the `int32` equality graph,
/// scalar evidence, exact constants, truth nodes), which read that
/// spelling: [`narrow_comparison_as_int32`], unless it folds to a constant.
/// Each index files it inside its own adjuster, so assuming, forgetting and
/// rebuilding a fact agree.
pub(crate) fn narrow_fact_widening(condition: &ConditionTerm) -> Option<ConditionTerm> {
    narrow_comparison_as_int32(condition)
        .filter(|widened| !matches!(widened, ConditionTerm::Constant(_)))
}

/// The native 8- or 16-bit comparison a promoted `int32` comparison of
/// widenings from one narrow format is the same fact as (rule K8), spelled
/// natively: the reverse of [`narrow_comparison_as_int32`], read through
/// [`ConditionTerm::comparison_fact`]. A Rust comparison of two narrow
/// values states this native comparison. `None` for any other condition.
pub(crate) fn native_narrow_comparison(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        ..
    } = condition
    else {
        return None;
    };
    let (format, relation, left, right) = condition.comparison_fact()?;
    (format.format().bits() < 32).then(|| {
        ConditionTerm::narrow_compare(
            format,
            relation,
            left.term(format).into_owned(),
            right.term(format).into_owned(),
        )
    })
}

/// [`narrow_comparison_as_int32`] of a condition fact, with its truth.
pub(crate) fn narrow_proposition_as_int32(proposition: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    narrow_comparison_as_int32(condition).map(|widened| Proposition::ConditionIs(widened, *value))
}

/// C compares an 8- or 16-bit value through its widening to `int32`
/// (rule C2): a signed 32-bit comparison whose sides are each such a
/// widening or a constant, at least one a widening, is the Integer
/// comparison of the sides' values, which a widening preserves (K8):
/// `0 <= widen(x)` is `0 <= to_integer(x as int32)`, which the Integer
/// engines read as `0 <= to_integer(x)` (rule W: a widening's observation is
/// built as written and read through to its operand's), so there is one
/// reading. One match on the two sides.
fn integer_comparisons_of_widenings(condition: &ConditionTerm, value: bool) -> Vec<Proposition> {
    use crate::kernel::CompareRelation as R;
    let ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation,
        left,
        right,
    } = condition
    else {
        return Vec::new();
    };
    let widening = |side: &Bitvector32Term| side.narrow_widening32_operand().is_some();
    if !widening(left) && !widening(right) {
        return Vec::new();
    }
    let side = |term: &Bitvector32Term| -> Option<SharedIntegerTerm> {
        if !widening(term) && term.constant32().is_none() {
            return None;
        }
        IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone()).map(Into::into)
    };
    let (Some(l), Some(r)) = (side(left), side(right)) else {
        return Vec::new();
    };
    let (condition, truth) = match (relation, value) {
        (R::Equal, truth) => (ConditionTerm::IntegerEqual(l, r), truth),
        (R::LessThan, true) | (R::GreaterEqual, false) => {
            (ConditionTerm::IntegerLessThan(l, r), true)
        }
        (R::LessEqual, true) | (R::GreaterThan, false) => {
            (ConditionTerm::IntegerLessEqual(l, r), true)
        }
        (R::GreaterThan, true) | (R::LessEqual, false) => {
            (ConditionTerm::IntegerLessThan(r, l), true)
        }
        (R::GreaterEqual, true) | (R::LessThan, false) => {
            (ConditionTerm::IntegerLessEqual(r, l), true)
        }
    };
    vec![Proposition::ConditionIs(condition, truth)]
}

/// The Integer comparisons of exact observations whose native comparison
/// ([`native_comparison_of_integer_observation`]) is exactly `proposition`,
/// a native comparison fact: `1u32 <= x` gives `1 <= to_integer(x)`. Each
/// candidate is recomputed through the forward map, so only exact
/// converses, up to the fact's equivalent order spellings, are returned. A
/// 32-bit word equality may read as `int32` or as `uint32`
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
            IntegerTerm::from_machine(ty, left.clone()),
            IntegerTerm::from_machine(ty, right.clone()),
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
            if native_comparison_at_format(&candidate, truth).is_some_and(
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
