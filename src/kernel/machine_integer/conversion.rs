//! Conversion: `to_integer(cast(S -> F, v)) == to_integer(v)` when
//! `to_integer(v)` lies in `F`. Every conversion is modular, so its result
//! is the one element of `F` congruent to `v` modulo `2^w`; when `v` lies
//! in `F` that element is `v`. When `F` contains `S` every value of `S`
//! lies in `F`, so widening needs no premise; a narrowing needs the range.
//!
//! The certificate rule `integer_cast_identity` checks this statement for
//! the conversion its observation names ([`cast`] gives the format the
//! operand's two bounds must lie in). A widening's bounds are the operand's
//! own range, which the type-range rule states with no premise. Which nodes spell a conversion is the term
//! representation's business (`representation::low_word`,
//! `representation::has_legacy_conversions`).

use super::representation;
use crate::kernel::{Bitvector32Term, IntegerTerm, MachineIntegerType, Proposition};

/// The candidate operands a cast identity for `observed` may name: each
/// observation `to_integer(x)` with `observed` the modulo conversion of `x`
/// this rule accepts. A 64-to-32-bit word narrowing does not record its
/// operand's signedness, so it has both readings.
pub(crate) fn cast_operands(observed: &IntegerTerm) -> Vec<IntegerTerm> {
    use MachineIntegerType as Ty;
    let IntegerTerm::Machine(machine) = observed else {
        return Vec::new();
    };
    let candidates: Vec<(Ty, &Bitvector32Term)> = match machine.value() {
        Bitvector32Term::MachineIntegerCast { value, source, .. } => vec![(*source, value)],
        Bitvector32Term::UInt32From64(value) => vec![(Ty::UInt64, value), (Ty::Int64, value)],
        // The legacy 32-to-64-bit conversions name their source's width,
        // and some their signedness; the cast rule below keeps the reading
        // it accepts.
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value) => vec![(Ty::Int32, value), (Ty::UInt32, value)],
        Bitvector32Term::UInt64FromInt64(value) => vec![(Ty::Int64, value)],
        _ => Vec::new(),
    };
    candidates
        .into_iter()
        .filter_map(|(ty, value)| IntegerTerm::from_machine(ty, value.clone()))
        .filter(|original| original != observed && cast(observed, original).is_some())
        .collect()
}

/// The word through which `observed`, at a format of more than 16 bits,
/// may read a narrow value: its own word up to 32 bits, or the operand of
/// a 32-to-64-bit conversion. A narrow observation of that word is the
/// candidate operand of a widening identity ([`narrow_widening`]).
pub(crate) fn widened_narrow_word(observed: &IntegerTerm) -> Option<&Bitvector32Term> {
    let IntegerTerm::Machine(machine) = observed else {
        return None;
    };
    match machine.ty().format().bits() {
        16 | 32 => Some(machine.value()),
        64 => match machine.value() {
            Bitvector32Term::Int64From32(word)
            | Bitvector32Term::UInt64FromInt32(word)
            | Bitvector32Term::Int64FromUInt32(word)
            | Bitvector32Term::UInt64From32(word) => Some(word),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `observed` reads the narrow value `original` at a format that
/// contains it: the same word, or the C widening conversion of that word.
///
/// A narrow value's word is the canonical carrier of its format, its sign
/// or zero extension (`docs/internals/kernel.md`), so a containing format of
/// at most 32 bits reads the same value from the same word, and a 64-bit
/// one reads it from the sign extension of the word, or for an unsigned
/// value from its zero extension. No bounds are needed for the identity;
/// the certificate's two bounds are still checked as for any cast.
///
/// The kernel does not assume the invariant of a term merely at a narrow
/// format. The word is either built as a carrier
/// ([`narrow_word_is_syntactic_carrier`](crate::kernel::primitives::narrow_word_is_syntactic_carrier)),
/// or it is a binder, an unregistered variable, whose range the
/// certificate's bounds must then state ([`narrow_binder_word`]).
pub(crate) fn narrow_widening(observed: &IntegerTerm, original: &IntegerTerm) -> bool {
    let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) = (observed, original)
    else {
        return false;
    };
    let (source, destination) = (operand.ty().format(), machine.ty().format());
    if source.bits() >= 32 || destination == source || !destination.contains(source) {
        return false;
    }
    let word = operand.value();
    if !crate::kernel::primitives::narrow_word_is_syntactic_carrier(operand.ty(), word)
        && binder_word(word).is_none()
    {
        return false;
    }
    match machine.value() {
        value if destination.bits() <= 32 => value == word,
        Bitvector32Term::Int64From32(inner) | Bitvector32Term::UInt64FromInt32(inner) => {
            inner.as_ref() == word
        }
        Bitvector32Term::Int64FromUInt32(inner) | Bitvector32Term::UInt64From32(inner) => {
            !source.is_signed() && inner.as_ref() == word
        }
        _ => false,
    }
}

/// A word that is a binder: a variable that is not a registered load.
fn binder_word(word: &Bitvector32Term) -> Option<&Bitvector32Term> {
    match word {
        Bitvector32Term::Variable(variable)
            if crate::kernel::registered_load_kind_for_variable(variable).is_none() =>
        {
            Some(word)
        }
        _ => None,
    }
}

/// For a widening ([`narrow_widening`]) of a narrow binder, the `int32`
/// observation of its word and the narrow range it must be bounded in.
///
/// A binder's word is the canonical carrier only through the range its
/// introduction states, `lo <= w` and `w <= hi` read at `int32`
/// (`c_narrow_integer_range_facts`). So a widening of one cites those two
/// facts as its bounds, inside the source's range, instead of bounds on the
/// narrow observation, which say nothing of an unextended word.
pub(crate) fn narrow_binder_word(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<(IntegerTerm, crate::kernel::primitives::MachineIntegerFormat)> {
    let IntegerTerm::Machine(operand) = original else {
        return None;
    };
    let word = binder_word(operand.value())?;
    if !narrow_widening(observed, original)
        || crate::kernel::primitives::narrow_word_is_syntactic_carrier(operand.ty(), word)
    {
        return None;
    }
    let observation = IntegerTerm::from_machine(MachineIntegerType::Int32, word.clone())?;
    Some((observation, operand.ty().format()))
}

/// For a widening of a narrow binder, the lower and upper range facts its
/// introduction filed (`c_narrow_integer_range_facts`), exactly as filed:
/// the native `int32` comparisons `w >= lo` and `w <= hi`. A certificate
/// cites these as the widening's bounds; the checker reads each as its
/// `int32` observation, `lo <= int32(w)` and `int32(w) <= hi`.
pub(crate) fn narrow_binder_range_facts(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<(Proposition, Proposition)> {
    narrow_binder_word(observed, original)?;
    let IntegerTerm::Machine(operand) = original else {
        return None;
    };
    let mut facts = crate::kernel::c_narrow_integer_range_facts(
        &operand.ty().value_from_term(operand.value().clone()),
    )?
    .into_iter();
    Some((facts.next()?, facts.next()?))
}

pub(crate) fn cast(
    observed: &IntegerTerm,
    original: &IntegerTerm,
) -> Option<crate::kernel::primitives::MachineIntegerFormat> {
    if narrow_widening(observed, original) {
        let IntegerTerm::Machine(machine) = observed else {
            unreachable!("a widening observes a machine value");
        };
        return Some(machine.ty().format());
    }
    let (IntegerTerm::Machine(machine), IntegerTerm::Machine(operand)) = (observed, original)
    else {
        return None;
    };
    // A C conversion node over a 32-bit carrier whose type contains the
    // destination (`(uint16)(int32)w`) is transparent here: every value
    // of the destination has the same word in both types, so once the
    // inner carrier is shown below to be the source's value inside the
    // destination range, the conversion leaves that word unchanged.
    // The same bounds are still required.
    if let Bitvector32Term::MachineIntegerCast {
        value: inner,
        source: through,
        destination,
    } = machine.value()
        && *destination == machine.ty()
        && through.format().bits() <= 32
        && through.format().contains(destination.format())
        && let Some(peeled) = IntegerTerm::from_machine(machine.ty(), inner.as_ref().clone())
        && let Some(format) = cast(&peeled, original)
    {
        return Some(format);
    }
    if !operand.ty().accepts_cast_operand(operand.value()) {
        return None;
    }
    // Compare with the canonical conversion of the *observed* source.
    // A narrowing cast can discard an intermediate widening/reinterpretation
    // node, so inspecting only the outer node loses the source named by the
    // certificate. The canonical cast still has exactly its modulo semantics;
    // the bounds below establish that this conversion preserves the value.
    let converted =
        Bitvector32Term::machine_integer_cast(operand.ty(), machine.ty(), operand.value().clone());
    // An `int32` or `uint32` observation reads σ(x) as `x` (rule K2), so
    // the canonical conversion is compared by its word.
    if machine.value() == &converted
        || machine.value() == converted.word32()
        || machine
            .value()
            .constant32()
            .is_some_and(|bits| converted.constant32() == Some(bits))
    {
        return Some(machine.ty().format());
    }
    // Ordinary C and the 32/64-bit modulo boundary retain legacy cast
    // terms. Compare against that same typed conversion policy, rather
    // than treating their numeric observation as a typed wide cast. The
    // explicit source bounds below remain mandatory for either spelling.
    let legacy_type = representation::has_legacy_conversions;
    // A narrowed byte/short value can retain the same 32-bit carrier, or
    // the low word of a 64-bit source, instead of an explicit narrowing
    // node. This direction still owes bounds on the word observation,
    // checked below against the narrow destination range; within it the
    // carrier is the destination's value, signed or unsigned. Bounds on
    // the narrow observation alone cannot justify interpreting an
    // arbitrary carrier as a word.
    let carrier = representation::low_word(operand.ty(), operand.value());
    if carrier.as_ref() == Some(machine.value()) && machine.ty().format().bits() < 32 {
        return Some(machine.ty().format());
    }
    // Sub-word byte stores retain an unsigned low-bit mask in their
    // 32-bit carrier. Promoting that canonical carrier to a word keeps
    // its mathematical value. An arbitrary sub-word-tagged variable is
    // insufficient: its carrier has not established the narrow range.
    let narrow_unsigned =
        |ty: MachineIntegerType| ty.format().bits() < 32 && !ty.format().is_signed();
    let masked_unsigned_source = match (operand.ty(), operand.value()) {
        (ty, Bitvector32Term::BitwiseAnd(left, right)) if narrow_unsigned(ty) => {
            let mask = (1u32 << operand.ty().format().bits()) - 1;
            matches!(left.as_ref(), Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) if *value == mask)
                || matches!(right.as_ref(), Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) if *value == mask)
        }
        _ => false,
    };
    let promoted_unsigned_source = masked_unsigned_source && machine.ty().format().bits() == 32;
    if (legacy_type(operand.ty()) && legacy_type(machine.ty())) || promoted_unsigned_source {
        let legacy = machine
            .ty()
            .convert_modulo_value(operand.ty().value_from_term(operand.value().clone()));
        if legacy == Some(machine.ty().value_from_term(machine.value().clone()))
            || legacy.as_ref().is_some_and(|value| {
                matches!(
                    value.numeric_value(),
                    crate::kernel::integer_c_value!(term) if term.word32() == machine.value()
                        || machine.value().constant32().is_some_and(|bits| term.constant32() == Some(bits))
                )
            })
        {
            return Some(machine.ty().format());
        }
    }
    // Typed byte stores/readback represent unsigned sub-word values by
    // retaining their low bits. This is the same modulo conversion from a
    // u32 word, with the source bounds still required below.
    if operand.ty() == MachineIntegerType::UInt32
        && narrow_unsigned(machine.ty())
        && let Bitvector32Term::BitwiseAnd(left, right) = machine.value()
    {
        let mask = (1u32 << machine.ty().format().bits()) - 1;
        let matches = |value: &Bitvector32Term, bits: &Bitvector32Term| {
            value == operand.value() && bits == &Bitvector32Term::Constant(mask)
        };
        if matches(left, right) || matches(right, left) {
            return Some(machine.ty().format());
        }
    }
    None
}
