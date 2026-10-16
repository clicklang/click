//! The carrier width of a machine-integer term.
//!
//! `Bitvector32Term` is the one term arena for every C integer and float
//! value, and it does not record a width. Width is implied: by the operator
//! family (`Add` is 32-bit, `Int64Add` and `UInt64Add` are 64-bit), by a
//! constant's shape, by a load's kind, and by a cast's or conversion's
//! destination. Narrow values (8 and 16 bits, and `_Bool`) ride in the
//! 32-bit carrier, and floats ride in the carrier of their bit width.
//!
//! This module infers that implied width and reports where a term disagrees
//! with itself, with its `CValue` tag, or with the comparison it sits in. It
//! changes no representation: it states the invariant that a width-carrying
//! integer term will make structural (`issues/one-integer-term-type.md`).

use super::*;

/// The width of the carrier a term's value occupies.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum CarrierWidth {
    Bits32,
    Bits64,
    Bits128,
}

impl CarrierWidth {
    fn of_bits(bits: u32) -> Self {
        match bits {
            0..=32 => Self::Bits32,
            33..=64 => Self::Bits64,
            _ => Self::Bits128,
        }
    }

    pub(crate) fn of_machine_type(integer_type: MachineIntegerType) -> Self {
        Self::of_bits(integer_type.format().bits())
    }

    fn of_load(kind: LoadKind) -> Self {
        match kind {
            LoadKind::Int8
            | LoadKind::UInt8
            | LoadKind::Int16
            | LoadKind::UInt16
            | LoadKind::Bits32
            | LoadKind::Float32 => Self::Bits32,
            LoadKind::Bits64 | LoadKind::Float64 => Self::Bits64,
            LoadKind::Int128 | LoadKind::UInt128 => Self::Bits128,
        }
    }

    /// The carrier a value of this tag occupies, or `None` for a value that
    /// is not a machine scalar.
    pub(crate) fn of_value(value: &CValue) -> Option<Self> {
        Some(match value.numeric_value() {
            CValue::PointerInteger(_) => unreachable!("numeric projection"),
            CValue::Bool(_)
            | CValue::Int8(_)
            | CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
            | CValue::Float32(_) => Self::Bits32,
            CValue::Int64(_) | CValue::UInt64(_) | CValue::Float64(_) => Self::Bits64,
            CValue::Int128(_) | CValue::UInt128(_) => Self::Bits128,
            CValue::Void | CValue::Pointer(_) => return None,
        })
    }
}

/// A place where a term's implied widths disagree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct WidthMismatch {
    /// The node whose operand or context disagrees, e.g. `Int64Add`.
    pub(crate) site: &'static str,
    pub(crate) expected: CarrierWidth,
    pub(crate) found: CarrierWidth,
}

impl std::fmt::Display for WidthMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: expected a {:?} carrier, found {:?}",
            self.site, self.expected, self.found
        )
    }
}

type WidthResult = Result<Option<CarrierWidth>, WidthMismatch>;

thread_local! {
    /// While `condition_variable_widths` runs, the width each variable meets
    /// at a typed position. Empty otherwise.
    static COLLECTED: std::cell::RefCell<Option<Vec<(Variable, CarrierWidth)>>> =
        const { std::cell::RefCell::new(None) };
}

/// Records that `variable` sits where a `width` carrier is expected.
fn note_variable(variable: Variable, width: CarrierWidth) -> Result<(), WidthMismatch> {
    COLLECTED.with(|collected| {
        if let Some(collected) = collected.borrow_mut().as_mut() {
            collected.push((variable, width));
        }
    });
    Ok(())
}

/// The width each variable of a condition is used at, or the first place
/// the condition's widths disagree. A variable used at two widths within the
/// one condition is such a place.
pub(crate) fn condition_variable_widths(
    condition: &ConditionTerm,
) -> Result<Vec<(Variable, CarrierWidth)>, WidthMismatch> {
    let previous = COLLECTED.with(|collected| collected.replace(Some(Vec::new())));
    let mismatch = condition_width_mismatch(condition);
    let mut widths = COLLECTED
        .with(|collected| collected.replace(previous))
        .unwrap_or_default();
    if let Some(mismatch) = mismatch {
        return Err(mismatch);
    }
    widths.sort_unstable();
    widths.dedup();
    for pair in widths.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(variable_conflict(pair[0].1, pair[1].1));
        }
    }
    Ok(widths)
}

/// A variable used at `found` where it was used at `first` before.
pub(crate) fn variable_conflict(first: CarrierWidth, found: CarrierWidth) -> WidthMismatch {
    WidthMismatch {
        site: "a variable used at another width than before",
        expected: first,
        found,
    }
}

fn expect(
    site: &'static str,
    expected: CarrierWidth,
    term: &Bitvector32Term,
) -> Result<(), WidthMismatch> {
    if let Bitvector32Term::Variable(variable) = term {
        return note_variable(*variable, expected);
    }
    match term_width(term)? {
        Some(found) if found != expected => Err(WidthMismatch {
            site,
            expected,
            found,
        }),
        _ => Ok(()),
    }
}

fn operands(site: &'static str, width: CarrierWidth, terms: &[&Bitvector32Term]) -> WidthResult {
    for term in terms {
        expect(site, width, term)?;
    }
    Ok(Some(width))
}

/// Unifies two widths that must agree, such as the arms of an `If`.
fn unify(
    site: &'static str,
    left: Option<CarrierWidth>,
    right: Option<CarrierWidth>,
) -> WidthResult {
    match (left, right) {
        (Some(left), Some(right)) if left != right => Err(WidthMismatch {
            site,
            expected: left,
            found: right,
        }),
        (Some(width), _) | (_, Some(width)) => Ok(Some(width)),
        (None, None) => Ok(None),
    }
}

/// The carrier width a term implies, `None` where nothing in the term fixes
/// it (a bare variable, a pointer address, a function application), or the
/// first place its widths disagree.
pub(crate) fn term_width(term: &Bitvector32Term) -> WidthResult {
    use Bitvector32Term as T;
    use CarrierWidth::{Bits32, Bits64};
    match term {
        T::Constant(_) => Ok(Some(Bits32)),
        T::Int64Constant(_) | T::UInt64Constant(_) => Ok(Some(Bits64)),
        T::MachineIntegerConstant(constant) => {
            Ok(Some(CarrierWidth::of_bits(constant.format().bits())))
        }
        T::Variable(_) | T::PointerAddress(_) => Ok(None),
        T::Add(l, r)
        | T::Subtract(l, r)
        | T::Multiply(l, r)
        | T::Divide(l, r)
        | T::UnsignedDivide(l, r)
        | T::Remainder(l, r)
        | T::UnsignedRemainder(l, r)
        | T::ShiftLeft(l, r)
        | T::ArithmeticShiftRight(l, r)
        | T::LogicalShiftRight(l, r)
        | T::BitwiseAnd(l, r)
        | T::BitwiseOr(l, r)
        | T::BitwiseXor(l, r) => operands("32-bit operator", Bits32, &[l, r]),
        T::BitwiseNot(value) => operands("32-bit operator", Bits32, &[value]),
        T::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_width_mismatch(condition).map_or(Ok(()), Err)?;
            let width = unify("If arms", term_width(then_term)?, term_width(else_term)?)?;
            if let Some(width) = width {
                expect("If arms", width, then_term)?;
                expect("If arms", width, else_term)?;
            }
            Ok(width)
        }
        T::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            unify("RangeFold bounds", term_width(start)?, term_width(end)?)?;
            unify("RangeFold value", term_width(initial)?, term_width(body)?)
        }
        T::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                term_width(argument)?;
            }
            Ok(None)
        }
        T::ClickFunctionApplication { .. } | T::AlgebraicMatch { .. } => Ok(None),
        T::MemoryLoad(_, _, kind) => Ok(Some(CarrierWidth::of_load(*kind))),
        T::IntegerToMachine { destination, .. } => {
            Ok(Some(CarrierWidth::of_machine_type(*destination)))
        }
        T::MachineIntegerCast {
            value,
            source,
            destination,
        } => {
            expect(
                "MachineIntegerCast operand",
                CarrierWidth::of_machine_type(*source),
                value,
            )?;
            Ok(Some(CarrierWidth::of_machine_type(*destination)))
        }
        T::Int64From32(value)
        | T::UInt64From32(value)
        | T::Int64FromUInt32(value)
        | T::UInt64FromInt32(value) => {
            expect("32-to-64-bit conversion", Bits32, value)?;
            Ok(Some(Bits64))
        }
        T::UInt32From64(value) => {
            expect("64-to-32-bit conversion", Bits64, value)?;
            Ok(Some(Bits32))
        }
        T::UInt64FromInt64(value) => operands("64-bit conversion", Bits64, &[value]),
        T::Int64Add(l, r)
        | T::Int64Subtract(l, r)
        | T::Int64Multiply(l, r)
        | T::Int64Divide(l, r)
        | T::Int64Remainder(l, r)
        | T::Int64BitwiseAnd(l, r)
        | T::Int64BitwiseOr(l, r)
        | T::Int64BitwiseXor(l, r)
        | T::UInt64Add(l, r)
        | T::UInt64Subtract(l, r)
        | T::UInt64Multiply(l, r)
        | T::UInt64Divide(l, r)
        | T::UInt64Remainder(l, r)
        | T::UInt64BitwiseAnd(l, r)
        | T::UInt64BitwiseOr(l, r)
        | T::UInt64BitwiseXor(l, r) => operands("64-bit operator", Bits64, &[l, r]),
        // A shift count is its own operand: C promotes it separately.
        T::Int64ShiftLeft(value, count)
        | T::Int64ArithmeticShiftRight(value, count)
        | T::UInt64ShiftLeft(value, count)
        | T::UInt64LogicalShiftRight(value, count) => {
            term_width(count)?;
            operands("64-bit shift", Bits64, &[value])
        }
        T::Int64BitwiseNot(value) | T::UInt64BitwiseNot(value) => {
            operands("64-bit operator", Bits64, &[value])
        }
        T::Float32Negate(value) => operands("float32 operator", Bits32, &[value]),
        T::Float32Binary { left, right, .. } => {
            operands("float32 operator", Bits32, &[left, right])
        }
        T::Float64Negate(value) => operands("float64 operator", Bits64, &[value]),
        T::Float64Binary { left, right, .. } => {
            operands("float64 operator", Bits64, &[left, right])
        }
    }
}

/// Where a `CValue`'s term disagrees with its tag or with itself.
pub(crate) fn value_width_mismatch(value: &CValue) -> Option<WidthMismatch> {
    let expected = CarrierWidth::of_value(value)?;
    let term = match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Void | CValue::Pointer(_) => return None,
        CValue::Bool(term)
        | CValue::Int8(term)
        | CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Int128(term)
        | CValue::UInt128(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => term,
    };
    expect(value_site(value), expected, term).err()
}

fn value_site(value: &CValue) -> &'static str {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Bool(_) => "CValue::Bool",
        CValue::Int8(_) => "CValue::Int8",
        CValue::Int16(_) => "CValue::Int16",
        CValue::Int32(_) => "CValue::Int32",
        CValue::UInt8(_) => "CValue::UInt8",
        CValue::UInt16(_) => "CValue::UInt16",
        CValue::UInt32(_) => "CValue::UInt32",
        CValue::Int64(_) => "CValue::Int64",
        CValue::UInt64(_) => "CValue::UInt64",
        CValue::Int128(_) => "CValue::Int128",
        CValue::UInt128(_) => "CValue::UInt128",
        CValue::Float32(_) => "CValue::Float32",
        CValue::Float64(_) => "CValue::Float64",
        CValue::Void | CValue::Pointer(_) => "CValue",
    }
}

/// Where a condition's operands disagree with the width its comparison
/// names, or with themselves.
pub(crate) fn condition_width_mismatch(condition: &ConditionTerm) -> Option<WidthMismatch> {
    use CarrierWidth::{Bits32, Bits64};
    use ConditionTerm as C;
    // A load equation names what a load reads: a store fact `load == v` or a
    // load variable's defining fact `x == load`. It is written with the
    // 32-bit equality whatever the load's width, so its two sides need only
    // agree with each other.
    if let C::Bitvector32Equal(left, right) = condition
        && (matches!(left.as_ref(), Bitvector32Term::MemoryLoad(..))
            || matches!(right.as_ref(), Bitvector32Term::MemoryLoad(..)))
    {
        return term_width(left)
            .and_then(|left| unify("load equation", left, term_width(right)?))
            .err();
    }
    let (site, width, left, right) = match condition {
        C::Bitvector32SignedLessThan(l, r)
        | C::Bitvector32SignedLessEqual(l, r)
        | C::Bitvector32SignedGreaterThan(l, r)
        | C::Bitvector32SignedGreaterEqual(l, r)
        | C::Bitvector32Equal(l, r)
        | C::Bitvector32SignedAddOverflows(l, r)
        | C::Bitvector32SignedSubtractOverflows(l, r)
        | C::Bitvector32SignedMultiplyOverflows(l, r)
        | C::Bitvector32SignedDivideOverflows(l, r) => ("32-bit comparison", Bits32, l, r),
        C::Bitvector32SignedShiftLeftOverflows(l, r) => {
            return term_width(r)
                .err()
                .or_else(|| expect("32-bit shift overflow", Bits32, l).err());
        }
        C::Bitvector64SignedLessThan(l, r)
        | C::Bitvector64SignedLessEqual(l, r)
        | C::Bitvector64SignedGreaterThan(l, r)
        | C::Bitvector64SignedGreaterEqual(l, r)
        | C::Bitvector64UnsignedLessThan(l, r)
        | C::Bitvector64UnsignedLessEqual(l, r)
        | C::Bitvector64UnsignedGreaterThan(l, r)
        | C::Bitvector64UnsignedGreaterEqual(l, r)
        | C::Bitvector64Equal(l, r)
        | C::Bitvector64SignedAddOverflows(l, r)
        | C::Bitvector64SignedSubtractOverflows(l, r)
        | C::Bitvector64SignedMultiplyOverflows(l, r)
        | C::Bitvector64SignedDivideOverflows(l, r) => ("64-bit comparison", Bits64, l, r),
        C::Bitvector64SignedShiftLeftOverflows(l, r) => {
            return term_width(r)
                .err()
                .or_else(|| expect("64-bit shift overflow", Bits64, l).err());
        }
        _ => return None,
    };
    expect(site, width, left)
        .and_then(|()| expect(site, width, right))
        .err()
}

/// Debug builds refuse a value or condition whose widths disagree where it
/// enters the kernel's state: a condition assumed into a fact context, a
/// value an expression evaluates to, and a value stored to memory. Release
/// builds skip the check.
#[track_caller]
pub(crate) fn debug_assert_widths(
    hook: &str,
    mismatch: impl FnOnce() -> Option<WidthMismatch>,
    subject: &dyn std::fmt::Debug,
) {
    if cfg!(debug_assertions)
        && let Some(mismatch) = mismatch()
    {
        let mut subject = format!("{subject:?}");
        subject.truncate(2000);
        panic!("integer width mismatch at {hook}: {mismatch}\nin {subject}");
    }
}

#[cfg(test)]
mod tests;
