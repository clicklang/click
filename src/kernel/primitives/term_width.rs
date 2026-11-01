//! The carrier width of a machine-integer term.
//!
//! `Bitvector32Term` is the one term arena for every C integer and float
//! value, and it does not record a width. Width is implied: by the operator
//! family (`Add` is 32-bit, `Binary` carries its 64-bit format), by a
//! constant's shape, by a load's kind, and by a cast's or conversion's
//! destination. Narrow values (8 and 16 bits, and `_Bool`) ride in the
//! 32-bit carrier, and floats ride in the carrier of their bit width.
//!
//! This module infers that implied width and reports where a term disagrees
//! with itself, with its `CValue` tag, or with the comparison it sits in. It
//! changes no representation: the rulings in `design/typed-indices.md`
//! explain why the width stays implied and is checked here instead.

use super::*;
use crate::kernel::unary_term;
use crate::kernel::{CompareRelation, MachineBinaryOp, OverflowOperation};

/// The width of the carrier a term's value occupies.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum CarrierWidth {
    /// An 8-bit value of its own: an `int8` or `uint8` value, read, constant
    /// or operator.
    Bits8,
    /// A 16-bit value of its own, a native narrow node.
    Bits16,
    Bits32,
    Bits64,
    Bits128,
}

impl CarrierWidth {
    fn of_bits(bits: u32) -> Self {
        match bits {
            0..=8 => Self::Bits8,
            9..=16 => Self::Bits16,
            17..=32 => Self::Bits32,
            33..=64 => Self::Bits64,
            _ => Self::Bits128,
        }
    }

    pub(crate) fn of_machine_type(integer_type: MachineIntegerType) -> Self {
        Self::of_bits(integer_type.format().bits())
    }

    /// The width of a node of `format`: [`Self::of_machine_type`].
    pub(crate) fn native(format: MachineIntegerType) -> Self {
        Self::of_machine_type(format)
    }

    fn of_load(kind: LoadKind) -> Self {
        match kind {
            LoadKind::Int8 | LoadKind::UInt8 => Self::Bits8,
            LoadKind::Int16 | LoadKind::UInt16 => Self::Bits16,
            LoadKind::Int32 | LoadKind::UInt32 | LoadKind::Float32 => Self::Bits32,
            LoadKind::Bits64 | LoadKind::Float64 => Self::Bits64,
            LoadKind::Int128 | LoadKind::UInt128 => Self::Bits128,
        }
    }

    /// The carrier a value of this tag occupies, or `None` for a value that
    /// is not a machine scalar.
    pub(crate) fn of_value(value: &CValue) -> Option<Self> {
        Some(match value.numeric_value() {
            CValue::PointerInteger(_) => unreachable!("numeric projection"),
            // A `Bool` travels as its 8-bit cast `b as uint8` (rule C1).
            CValue::Bool(_) | CValue::Int8(_) | CValue::UInt8(_) => Self::Bits8,
            CValue::Int16(_) | CValue::UInt16(_) => Self::Bits16,
            CValue::Int32(_) | CValue::UInt32(_) | CValue::Float32(_) => Self::Bits32,
            CValue::Int64(_) | CValue::UInt64(_) | CValue::Float64(_) => Self::Bits64,
            CValue::Int128(_) | CValue::UInt128(_) => Self::Bits128,
            CValue::Void | CValue::Pointer(_) | CValue::Parameter(_) => return None,
        })
    }
}

/// A place where a term's implied widths disagree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct WidthMismatch {
    /// The node whose operand or context disagrees, e.g. `64-bit operator`.
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

#[cfg(test)]
thread_local! {
    /// The nodes [`term_width`] and [`root_width`] have read on this thread,
    /// so a scaling test can bound the width reads of a hot path.
    pub(crate) static WIDTH_NODE_READS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Counts one node read by a width reader (tests only).
fn note_width_read() {
    #[cfg(test)]
    WIDTH_NODE_READS.with(|reads| reads.set(reads.get() + 1));
}

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

/// The width of a format-carrying operator ([`Bitvector32Term::Binary`],
/// [`Bitvector32Term::Unary`]) other than a 32-bit one: the 64-bit formats,
/// and the 8- and 16-bit formats' native sign-free operators
/// (`+ - * & | ^ <<` and `~`, [`is_native_narrow_operator`]). A node at any
/// other format, or a narrow node of another operator, is malformed, and is
/// reported as a 64-bit operator meeting the format's width.
fn machine_operator_width(
    site: &'static str,
    format: MachineIntegerType,
    narrow_operator: bool,
) -> Result<CarrierWidth, WidthMismatch> {
    match format {
        MachineIntegerType::Int64 | MachineIntegerType::UInt64 => Ok(CarrierWidth::Bits64),
        MachineIntegerType::Int8
        | MachineIntegerType::UInt8
        | MachineIntegerType::Int16
        | MachineIntegerType::UInt16
            if narrow_operator =>
        {
            Ok(CarrierWidth::native(format))
        }
        _ => Err(WidthMismatch {
            site,
            expected: CarrierWidth::Bits64,
            found: CarrierWidth::native(format),
        }),
    }
}

/// Whether an 8- or 16-bit format has a native node for `op`: the sign-free
/// operators `+ - * & | ^ <<` (decision G4). Division, remainder and right
/// shifts read a sign and stay promoted for now.
pub(crate) fn is_native_narrow_operator(op: MachineBinaryOp) -> bool {
    matches!(
        op,
        MachineBinaryOp::Add
            | MachineBinaryOp::Subtract
            | MachineBinaryOp::Multiply
            | MachineBinaryOp::BitwiseAnd
            | MachineBinaryOp::BitwiseOr
            | MachineBinaryOp::BitwiseXor
            | MachineBinaryOp::ShiftLeft
    )
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
    note_width_read();
    use CarrierWidth::{Bits32, Bits64};
    match term {
        T::Constant(_) | T::UInt32Constant(_) => Ok(Some(Bits32)),
        T::Int64Constant(_) | T::UInt64Constant(_) => Ok(Some(Bits64)),
        T::MachineIntegerConstant(constant) => Ok(Some(match constant.format().bits() {
            8 => CarrierWidth::Bits8,
            16 => CarrierWidth::Bits16,
            bits => CarrierWidth::of_bits(bits),
        })),
        T::Variable(_) | T::PointerAddress(_, _) => Ok(None),
        crate::kernel::binary_bitvector32_term!(l, r) => {
            operands("32-bit operator", Bits32, &[l, r])
        }
        unary_term!(Bits32, BitwiseNot, value) => operands("32-bit operator", Bits32, &[value]),
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
        // Rule C1: the cast's carrier is its format's; its operand is a
        // condition, whose own widths are checked.
        T::BoolCast { to, value } => {
            condition_width_mismatch(value).map_or(Ok(()), Err)?;
            Ok(Some(CarrierWidth::of_machine_type(*to)))
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
        T::Binary {
            format,
            op,
            left,
            right,
        } => {
            let width = machine_operator_width(
                "format-carrying binary operator",
                *format,
                is_native_narrow_operator(*op),
            )?;
            let (site, shift_site) = if width == Bits64 {
                ("64-bit operator", "64-bit shift")
            } else {
                ("narrow operator", "narrow shift")
            };
            // A shift count is its own operand: C promotes it separately.
            if matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight) {
                term_width(right)?;
                operands(shift_site, width, &[left])
            } else {
                operands(site, width, &[left, right])
            }
        }
        T::Unary {
            format,
            op,
            operand,
        } => {
            let width = machine_operator_width(
                "format-carrying unary operator",
                *format,
                *op == crate::kernel::MachineUnaryOp::BitwiseNot,
            )?;
            let site = if width == Bits64 {
                "64-bit operator"
            } else {
                "narrow operator"
            };
            operands(site, width, &[operand])
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

/// The carrier width a term's root node fixes, read from that node alone:
/// a constant by its shape, an operator or cast by its format or
/// destination, a load by its kind. `None` where the root does not fix it (a
/// variable, an application, an `If` or a fold, whose width lives in their
/// operands). O(1): unlike [`term_width`], it checks no operand, so a hot
/// path may call it once per interned node.
pub(crate) fn root_width(term: &Bitvector32Term) -> Option<CarrierWidth> {
    use Bitvector32Term as T;
    note_width_read();
    use CarrierWidth::{Bits32, Bits64};
    Some(match term {
        T::Constant(_) | T::UInt32Constant(_) => Bits32,
        T::Int64Constant(_) | T::UInt64Constant(_) => Bits64,
        T::MachineIntegerConstant(constant) => CarrierWidth::of_bits(constant.format().bits()),
        T::Variable(_)
        | T::PointerAddress(_, _)
        | T::If { .. }
        | T::RangeFold { .. }
        | T::PureFunctionApplication { .. }
        | T::ClickFunctionApplication { .. }
        | T::AlgebraicMatch { .. } => return None,
        crate::kernel::binary_bitvector32_term!(_l, _r) => Bits32,
        unary_term!(Bits32, BitwiseNot, _value) => Bits32,
        T::MemoryLoad(_, _, kind) => CarrierWidth::of_load(*kind),
        T::IntegerToMachine { destination, .. } => CarrierWidth::of_machine_type(*destination),
        T::BoolCast { to, .. } => CarrierWidth::of_machine_type(*to),
        T::MachineIntegerCast { destination, .. } => CarrierWidth::of_machine_type(*destination),
        T::Int64From32(_)
        | T::UInt64From32(_)
        | T::Int64FromUInt32(_)
        | T::UInt64FromInt32(_)
        | T::UInt64FromInt64(_) => Bits64,
        T::UInt32From64(_) => Bits32,
        T::Binary { format, .. } | T::Unary { format, .. } => CarrierWidth::native(*format),
        T::Float32Negate(_) | T::Float32Binary { .. } => Bits32,
        T::Float64Negate(_) | T::Float64Binary { .. } => Bits64,
    })
}

/// Where a `CValue`'s term disagrees with its tag or with itself.
pub(crate) fn value_width_mismatch(value: &CValue) -> Option<WidthMismatch> {
    let expected = CarrierWidth::of_value(value)?;
    let term = match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Void | CValue::Pointer(_) | CValue::Parameter(_) => return None,
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

/// A `_Bool` constant outside `0..=1`: a `Bool` rides zero-extended in a
/// 32-bit carrier. An 8- or 16-bit value is a value of its own format, whose
/// constant is in range by construction.
pub(crate) fn narrow_constant_out_of_range(value: &CValue) -> Option<NarrowRangeViolation> {
    let CValue::Bool(term) = value else {
        return None;
    };
    // A `Bool` constant is the `uint8` constant 0 or 1 (rule C1).
    let bits = term.narrow_constant_bits(crate::kernel::MachineIntegerType::UInt8)?;
    (bits > 1).then_some(NarrowRangeViolation {
        site: "CValue::Bool",
        bits: u32::try_from(bits).expect("an 8-bit constant"),
    })
}

/// A `Bool` constant whose carrier word lies outside its range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NarrowRangeViolation {
    pub(crate) site: &'static str,
    pub(crate) bits: u32,
}

impl std::fmt::Display for NarrowRangeViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: constant carrier word {:#x} is outside its type's range",
            self.site, self.bits
        )
    }
}

/// Every refusal for a value: its widths, then a `Bool` constant's range.
pub(crate) fn value_mismatch(value: &CValue) -> Option<String> {
    value_width_mismatch(value)
        .map(|mismatch| mismatch.to_string())
        .or_else(|| narrow_constant_out_of_range(value).map(|violation| violation.to_string()))
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
        CValue::Void | CValue::Pointer(_) | CValue::Parameter(_) => "CValue",
    }
}

/// Where a condition's operands disagree with the width its comparison
/// names, or with themselves.
pub(crate) fn condition_width_mismatch(condition: &ConditionTerm) -> Option<WidthMismatch> {
    use CarrierWidth::{Bits32, Bits64, Bits128};
    use ConditionTerm as C;
    // A load equation names what a load reads: a store fact `load == v` or a
    // load variable's defining fact `x == load`. It is written with the
    // 32-bit equality whatever the load's width, so its two sides need only
    // agree with each other.
    if let C::Compare {
        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
        relation: CompareRelation::Equal,
        left,
        right,
    } = condition
        && (matches!(left.as_ref(), Bitvector32Term::MemoryLoad(..))
            || matches!(right.as_ref(), Bitvector32Term::MemoryLoad(..)))
    {
        return term_width(left)
            .and_then(|left| unify("load equation", left, term_width(right)?))
            .err();
    }
    let (format, shift, left, right) = match condition {
        C::Compare {
            format,
            left,
            right,
            ..
        } => (*format, false, left, right),
        C::Overflows {
            format,
            op,
            left,
            right,
        } => (*format, *op == OverflowOperation::ShiftLeft, left, right),
        // A `Bool` conditional or equality is as well-formed as its parts.
        C::BoolIf { .. } | C::BoolEqual(..) => {
            return condition.bool_children().find_map(condition_width_mismatch);
        }
        _ => return None,
    };
    let (width, site, shift_site) = match CarrierWidth::of_bits(format.format().bits()) {
        Bits32 => (Bits32, "32-bit comparison", "32-bit shift overflow"),
        Bits64 => (Bits64, "64-bit comparison", "64-bit shift overflow"),
        Bits128 => (Bits128, "128-bit comparison", "128-bit shift overflow"),
        CarrierWidth::Bits8 => (
            CarrierWidth::Bits8,
            "8-bit comparison",
            "8-bit shift overflow",
        ),
        CarrierWidth::Bits16 => (
            CarrierWidth::Bits16,
            "16-bit comparison",
            "16-bit shift overflow",
        ),
    };
    // A shift count may have any width; the shifted operand has the
    // format's.
    if shift {
        return term_width(right)
            .err()
            .or_else(|| expect(shift_site, width, left).err());
    }
    expect(site, width, left)
        .and_then(|()| expect(site, width, right))
        .err()
}

/// Debug builds refuse a value or condition whose widths disagree where it
/// enters the kernel's state: a condition assumed into a fact context, a
/// value an expression evaluates to, and a value stored to memory. Release
/// builds skip the check.
#[track_caller]
pub(crate) fn debug_assert_widths<M: std::fmt::Display>(
    hook: &str,
    mismatch: impl FnOnce() -> Option<M>,
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
