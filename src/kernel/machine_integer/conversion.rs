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
//!
//! It is also the one conversion table of the languages
//! (`design/machine-integers.md`, "Conversions in the languages"): [`lower`]
//! says, for a source and destination format and a policy, which node a
//! conversion builds and whether it owes its range, and [`convert_term`]
//! builds that node. C's conversions (`narrow_integer`), C++20 integral
//! conversions and Rust `as` (`conversion::convert_value`)
//! build their terms here, so one conversion has one term in every
//! language. The policy changes only what the conversion owes, never its
//! term.

use super::representation;
use crate::kernel::binary_term;
use crate::kernel::{Bitvector32Term, CValue, IntegerTerm, MachineIntegerType, Proposition};

/// What a language conversion asks of its operand.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConversionPolicy {
    /// The value modulo 2^w of the destination width, owing nothing: C's
    /// conversion as GCC and Clang compile it (signed narrowing included,
    /// `design/machine-integers.md`, Decisions 2026-10-21), C++20 integral
    /// conversions and Rust `as`.
    Modular,
    /// A specification's conversion between machine types: the same term,
    /// owing the destination's range where [`Conversion::owes_range`] says.
    Checked,
}

/// The node a conversion builds, by source and destination format.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConversionLowering {
    /// The same format: the operand itself.
    Identity,
    /// `int32` to `uint32` or back: the sign cast σ (rules K1 to K4).
    SignCast,
    /// `MachineIntegerCast`: every conversion into an 8- or 16-bit format
    /// (its word is rule K7's), every widening of an 8- or 16-bit value into
    /// a 32-bit format (whose word is its operand's, rule K8), and every
    /// conversion involving 128 bits.
    Cast,
    /// A 64-bit value into a 32-bit format: its low word, `UInt32From64`.
    LowWord,
    /// A value of at most 32 bits into a 64-bit format: the legacy
    /// extension node of the source's and destination's signedness.
    Extend64,
    /// `int64` to `uint64` or back: the same 64 bits.
    Reinterpret64,
}

/// One entry of the conversion table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Conversion {
    pub(crate) lowering: ConversionLowering,
    /// Whether the conversion owes its operand's destination range: only a
    /// [`ConversionPolicy::Checked`] conversion that can change the value,
    /// into a signed destination other than by σ, or into an 8- or 16-bit
    /// unsigned one from at most 64 bits. Every other conversion is modular.
    pub(crate) owes_range: bool,
}

/// The conversion table: the node a conversion from `source` to
/// `destination` builds, and what it owes under `policy`. Width and
/// signedness checks only; no term is inspected.
pub(crate) fn lower(
    source: MachineIntegerType,
    destination: MachineIntegerType,
    policy: ConversionPolicy,
) -> Conversion {
    use ConversionLowering as L;
    let (from, to) = (source.format(), destination.format());
    let lowering = if source == destination {
        L::Identity
    } else if from.bits() == 128 || to.bits() == 128 || to.bits() < 32 {
        L::Cast
    } else if to.bits() == 32 {
        match from.bits() {
            64 => L::LowWord,
            32 => L::SignCast,
            _ => L::Cast,
        }
    } else if from.bits() == 64 {
        L::Reinterpret64
    } else {
        L::Extend64
    };
    let owes_range = policy == ConversionPolicy::Checked
        && !to.contains(from)
        && lowering != L::SignCast
        && (to.is_signed() || (to.bits() < 32 && from.bits() <= 64));
    Conversion {
        lowering,
        owes_range,
    }
}

/// C11 6.3.1.8, the usual arithmetic conversions, over formats in the LP64
/// model Click targets: the format two integer operands of formats `left`
/// and `right` are converted to. Each is first promoted (6.3.1.1): a format
/// of fewer than 32 bits, every value of which `int32` holds, to `int32`.
/// Then the two agree; or, of one signedness, the wider is taken; or the
/// unsigned one is taken when it is at least as wide as the signed one; or
/// the signed one when it holds every value of the unsigned one; or else
/// the unsigned format of the signed one's width. `None` for a 128-bit
/// operand, which no C operation here takes. Width and signedness checks
/// only.
pub(crate) fn usual_arithmetic_format(
    left: MachineIntegerType,
    right: MachineIntegerType,
) -> Option<MachineIntegerType> {
    let promote = |ty: MachineIntegerType| {
        if ty.format().bits() < 32 {
            MachineIntegerType::Int32
        } else {
            ty
        }
    };
    let (left, right) = (promote(left), promote(right));
    let (l, r) = (left.format(), right.format());
    if l.bits() > 64 || r.bits() > 64 {
        return None;
    }
    if left == right {
        return Some(left);
    }
    if l.is_signed() == r.is_signed() {
        return Some(if l.bits() >= r.bits() { left } else { right });
    }
    let (signed, unsigned) = if l.is_signed() {
        (left, right)
    } else {
        (right, left)
    };
    Some(if unsigned.format().bits() >= signed.format().bits() {
        unsigned
    } else if signed.format().contains(unsigned.format()) {
        signed
    } else {
        match signed {
            MachineIntegerType::Int32 => MachineIntegerType::UInt32,
            _ => MachineIntegerType::UInt64,
        }
    })
}

/// The term of the conversion of `value`, a term of `source`, to
/// `destination`, as [`lower`] says. A constant operand folds (the
/// constructors fold a root constant); nothing else is inspected, so the
/// work is constant whatever the operand's size, charged by the node's
/// constructor.
pub(crate) fn convert_term(
    source: MachineIntegerType,
    destination: MachineIntegerType,
    value: Bitvector32Term,
) -> Bitvector32Term {
    use ConversionLowering as L;
    let (from, to) = (source.format(), destination.format());
    match lower(source, destination, ConversionPolicy::Modular).lowering {
        L::Identity => value,
        L::SignCast => Bitvector32Term::sign_cast32(source, destination, value),
        L::Cast => Bitvector32Term::machine_integer_cast(source, destination, value),
        // A folded low word is a constant of the destination's format.
        L::LowWord => Bitvector32Term::uint32_from_64(value).in_format32(destination),
        L::Reinterpret64 if to.is_signed() => Bitvector32Term::int64_from_uint64_bits(value),
        L::Reinterpret64 => Bitvector32Term::uint64_from_int64(value),
        L::Extend64 => match (to.is_signed(), from.is_signed()) {
            (true, true) => Bitvector32Term::int64_from_32(value),
            (true, false) => Bitvector32Term::int64_from_uint32(value),
            (false, true) => Bitvector32Term::uint64_from_int32(value),
            (false, false) => Bitvector32Term::uint64_from_32(value),
        },
    }
}

/// The modular conversion of an evaluated, typed machine value to
/// `destination`: the one entry point of C++20 integral conversions and
/// Rust `as` (`conversion::convert_value`), and of C's
/// conversions involving 128 bits. A Boolean source observes its 0-or-1
/// value. A root constant folds exactly; a 128-bit conversion first checks
/// its operand's root (`accepts_cast_operand`). `None` for a value that is
/// not an integer.
pub(crate) fn convert_value(value: CValue, destination: MachineIntegerType) -> Option<CValue> {
    crate::instrumentation::record_deterministic_work(1);
    let value = value.numeric_value().clone();
    // Rule C1: a `Bool` converted to an integer is its cast at the
    // destination's format, 1 when it holds and 0 otherwise. It owes
    // nothing under either policy.
    if let CValue::Bool(word) = &value {
        return CValue::from_bitvector_term(
            destination.c_type(),
            crate::kernel::Bitvector32Term::bool_word_as(destination, word),
        );
    }
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let wide = source.format().bits() == 128 || destination.format().bits() == 128;
    if !wide {
        if let Some(constant) = source.constant_from_value(&value) {
            return destination.constant_value(constant.convert_modulo(destination.format()));
        }
        if source == destination {
            return Some(value);
        }
    }
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    // Root validation stays local even when an operand contains a large
    // legacy expression. Wide operands cannot reinterpret word nodes.
    if wide && !source.accepts_cast_operand(&term) {
        return None;
    }
    Some(destination.value_from_term(convert_term(source, destination, term)))
}

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
        // A 32-bit widening of a narrow value names its word (rule K8).
        16 | 32 => Some(machine.value().word32()),
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
        // The widening node, or the bare word, names the word (rule K8).
        value if destination.bits() <= 32 => value.word32() == word,
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
    // the canonical conversion is compared by its word. Only σ: a narrow
    // widening's word (rule K8) is its operand only for a canonical
    // carrier, which `narrow_widening` above establishes; comparing by that
    // word here would accept any word merely tagged narrow.
    if machine.value() == &converted
        || converted
            .sign_cast32_operand()
            .is_some_and(|(_, word)| machine.value() == word)
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
        (ty, binary_term!(Bits32, BitwiseAnd, left, right)) if narrow_unsigned(ty) => {
            let mask = (1u32 << operand.ty().format().bits()) - 1;
            matches!(left.as_ref(), Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) if *value == mask)
                || matches!(right.as_ref(), Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) if *value == mask)
        }
        _ => false,
    };
    let promoted_unsigned_source = masked_unsigned_source && machine.ty().format().bits() == 32;
    if (legacy_type(operand.ty()) && legacy_type(machine.ty())) || promoted_unsigned_source {
        let legacy = convert_value(
            operand.ty().value_from_term(operand.value().clone()),
            machine.ty(),
        );
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
        && let binary_term!(Bits32, BitwiseAnd, left, right) = machine.value()
    {
        let mask = (1u32 << machine.ty().format().bits()) - 1;
        let matches = |value: &Bitvector32Term, bits: &Bitvector32Term| {
            value == operand.value() && bits.constant32() == Some(mask)
        };
        if matches(left, right) || matches(right, left) {
            return Some(machine.ty().format());
        }
    }
    None
}
