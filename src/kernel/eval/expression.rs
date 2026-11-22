use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::MachineCastSpelling;
use crate::kernel::bits32_constant;
use crate::kernel::effective_type::CAccessClass;
use crate::kernel::primitives::float_conversion::{
    float32_to_integer_value, float64_to_integer_value, integer_to_float32_bits,
    integer_to_float64_bits,
};

fn integer_to_float_value(value: ProgramValue, target_type: ProgramType) -> Option<ProgramValue> {
    let (source_name, term) = match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Bool(term) => ("bool", term),
        ProgramValue::Int8(term) => ("int8", term),
        ProgramValue::Int16(term) => ("int16", term),
        ProgramValue::Int32(term) => ("int32", term),
        ProgramValue::UInt8(term) => ("uint8", term),
        ProgramValue::UInt16(term) => ("uint16", term),
        ProgramValue::UInt32(term) => ("uint32", term),
        ProgramValue::Int64(term) => ("int64", term),
        ProgramValue::UInt64(term) => ("uint64", term),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_)
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_) => return None,
    };
    let target_name = match target_type {
        ProgramType::Float32 => "float32",
        ProgramType::Float64 => "float64",
        _ => return None,
    };
    let term =
        MachineTerm::opaque_conversion(format!("c_{source_name}_to_{target_name}"), term.clone());
    Some(match target_type {
        ProgramType::Float32 => ProgramValue::Float32(term),
        ProgramType::Float64 => ProgramValue::Float64(term),
        _ => unreachable!(),
    })
}

fn add_float_to_integer_obligations(
    value: &MachineTerm,
    source_type: ProgramType,
    target_type: ProgramType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<()> {
    let (signed, bits) = match target_type {
        ProgramType::Int8 => (true, 8),
        ProgramType::Int16 => (true, 16),
        ProgramType::Int32 => (true, 32),
        ProgramType::Int64 => (true, 64),
        ProgramType::UInt8 => (false, 8),
        ProgramType::UInt16 => (false, 16),
        ProgramType::UInt32 => (false, 32),
        ProgramType::UInt64 => (false, 64),
        _ => return None,
    };
    let precision = match source_type {
        ProgramType::Float32 => f32::MANTISSA_DIGITS,
        ProgramType::Float64 => f64::MANTISSA_DIGITS,
        _ => return None,
    };
    // The ordered lower and upper comparisons also exclude NaN and infinities.
    let bound = |magnitude, negative, operator| {
        let condition = match source_type {
            ProgramType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                MachineTerm::constant(integer_to_float32_bits(negative, magnitude)),
                operator,
            ),
            ProgramType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                MachineTerm::uint64_constant(integer_to_float64_bits(negative, magnitude)),
                operator,
            ),
            _ => unreachable!(),
        };
        Proposition::condition_is(condition, true)
    };

    let minimum_magnitude = if signed { 1u128 << (bits - 1) } else { 0 };
    // Truncation admits values strictly above MIN - 1. If MIN - 1 is
    // unrepresentable, MIN is the next float above that threshold.
    let lower = if minimum_magnitude < (1u128 << precision) {
        // An exact premise at the stronger integral bound also proves this
        // side of the range. Look up just that bound, including +0 for unsigned.
        let integral_bound = bound(minimum_magnitude, signed, ComparisonOperator::GreaterEqual);
        if assumptions.proves_exact(&integral_bound) {
            None
        } else {
            Some(bound(
                minimum_magnitude + 1,
                true,
                ComparisonOperator::GreaterThan,
            ))
        }
    } else {
        Some(bound(
            minimum_magnitude,
            true,
            ComparisonOperator::GreaterEqual,
        ))
    };
    if let Some(lower) = lower {
        add_proof_obligation(obligations, assumptions, lower)?;
    }

    let upper_magnitude = 1u128 << if signed { bits - 1 } else { bits };
    add_proof_obligation(
        obligations,
        assumptions,
        bound(upper_magnitude, false, ComparisonOperator::LessThan),
    )
}

fn float_to_integer_conversion_value(
    value: MachineTerm,
    source_type: ProgramType,
    target_type: ProgramType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    add_float_to_integer_obligations(&value, source_type, target_type, obligations, assumptions)?;
    let source_name = match source_type {
        ProgramType::Float32 => "float32",
        ProgramType::Float64 => "float64",
        _ => return None,
    };
    let target_name = match target_type {
        ProgramType::Int8 => "int8",
        ProgramType::Int16 => "int16",
        ProgramType::Int32 => "int32",
        ProgramType::UInt8 => "uint8",
        ProgramType::UInt16 => "uint16",
        ProgramType::UInt32 => "uint32",
        ProgramType::Int64 => "int64",
        ProgramType::UInt64 => "uint64",
        _ => return None,
    };
    let term = MachineTerm::opaque_conversion(format!("c_{source_name}_to_{target_name}"), value);
    Some(match target_type {
        ProgramType::Int8 => ProgramValue::Int8(term),
        ProgramType::Int16 => ProgramValue::Int16(term),
        ProgramType::Int32 => ProgramValue::Int32(term),
        ProgramType::UInt8 => ProgramValue::UInt8(term),
        ProgramType::UInt16 => ProgramValue::UInt16(term),
        ProgramType::UInt32 => ProgramValue::UInt32(term),
        ProgramType::Int64 => ProgramValue::Int64(term),
        ProgramType::UInt64 => ProgramValue::UInt64(term),
        _ => unreachable!(),
    })
}

thread_local! {
    /// How many specification-fragment evaluations enclose the current read.
    static SPECIFICATION_READS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// How many evaluations of a specification's C operands, such as a
    /// resource argument, enclose the current read.
    static SPECIFICATION_ACCESSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Marks the reads made while it lives as specification reads. A
/// specification names values the program produced; reading one states
/// nothing new about it, so it files no range and gains no guard. Its reads
/// are also specification accesses ([`SpecificationAccessScope`]).
pub(in crate::kernel) struct SpecificationReadScope(SpecificationAccessScope);

impl SpecificationReadScope {
    pub(in crate::kernel) fn is_active() -> bool {
        SPECIFICATION_READS.with(|depth| depth.get() > 0)
    }

    pub(in crate::kernel) fn enter() -> Self {
        SPECIFICATION_READS.with(|depth| depth.set(depth.get() + 1));
        Self(SpecificationAccessScope::enter())
    }
}

impl Drop for SpecificationReadScope {
    fn drop(&mut self) {
        SPECIFICATION_READS.with(|depth| depth.set(depth.get() - 1));
    }
}

/// Marks the reads made while it lives as a specification's, such as the
/// reads of a resource argument or a contract's memory operand. Only C
/// accesses carry an access type: a specification reads memory as a value,
/// so the strict-aliasing check does not apply to it
/// (`design/effective-types.md`). The C program's own accesses are checked
/// where it makes them.
pub(in crate::kernel) struct SpecificationAccessScope(());

impl SpecificationAccessScope {
    pub(in crate::kernel) fn enter() -> Self {
        SPECIFICATION_ACCESSES.with(|depth| depth.set(depth.get() + 1));
        Self(())
    }

    pub(in crate::kernel) fn is_active() -> bool {
        SPECIFICATION_ACCESSES.with(|depth| depth.get() > 0)
    }
}

impl Drop for SpecificationAccessScope {
    fn drop(&mut self) {
        SPECIFICATION_ACCESSES.with(|depth| depth.set(depth.get() - 1));
    }
}

thread_local! {
    /// How many Rust `Bool` values (decision D5) enclose the current
    /// evaluation.
    static CONDITION_VALUES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Marks the evaluation of a Rust `Bool` value's operand (Stage 5, decision
/// D5): while it lives, a comparison, `!` or connective of simple operands
/// is the `Bool` it tests, carried as its cast `c as int32` (rule C1), the
/// same 1 or 0 C's operator yields, with no path split.
pub(in crate::kernel) struct ConditionValueScope(());

impl ConditionValueScope {
    pub(in crate::kernel) fn enter() -> Self {
        CONDITION_VALUES.with(|depth| depth.set(depth.get() + 1));
        Self(())
    }

    pub(in crate::kernel) fn is_active() -> bool {
        CONDITION_VALUES.with(|depth| depth.get() > 0)
    }
}

impl Drop for ConditionValueScope {
    fn drop(&mut self) {
        CONDITION_VALUES.with(|depth| depth.set(depth.get() - 1));
    }
}

thread_local! {
    static KEEP_WORD_REPRESENTATION: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

/// Publishing resource facts can observe a word numerically without recovering
/// a discarded carrier. Value checks retain whole values; an explicit pointer
/// cast restores that demand inside a numeric observation.
pub(in crate::kernel) struct WordRepresentationScope(bool);

impl WordRepresentationScope {
    pub(in crate::kernel) fn enter(keep: bool) -> Self {
        Self(KEEP_WORD_REPRESENTATION.with(|value| value.replace(keep)))
    }

    pub(in crate::kernel) fn keeps_representation() -> bool {
        KEEP_WORD_REPRESENTATION.with(std::cell::Cell::get)
    }
}

impl Drop for WordRepresentationScope {
    fn drop(&mut self) {
        KEEP_WORD_REPRESENTATION.with(|value| value.set(self.0));
    }
}

/// Files the range of a `Bool`'s cast where the value is produced, as
/// certified path facts (rule C1b). An 8- or 16-bit value is a value of its
/// own format, whose range is the format's, so nothing is filed for it.
///
/// The range is a consequence, not a premise: every producer of a narrow
/// value already established it (a conversion, which lands in the range, a
/// load of the narrow kind, a callee's return conversion), so the step's theorem
/// concludes it and no reader of the step owes a derivation of it. Being
/// public, it reaches every check that reads path facts -- a prerequisite
/// left to the proof, the owned-footprint check of a store. A range the
/// context already holds exactly is not refiled. Constructing this consequence
/// never asks the general condition solver to establish it again.
pub(in crate::kernel) fn add_narrow_integer_range_execution_pure_facts(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    value: &ProgramValue,
) {
    if SPECIFICATION_READS.with(|depth| depth.get() > 0) {
        return;
    }
    let Some(range_facts) = crate::kernel::program_bool_cast_range_facts(value) else {
        return;
    };
    for proposition in range_facts {
        if assumptions.proves_exact(&proposition)
            || facts.iter().any(|fact| fact.proposition() == &proposition)
        {
            continue;
        }
        facts.push(ExecutionPureFact::certified(proposition));
    }
}

/// C's integer promotion and usual arithmetic conversions: `value` read at
/// `destination`, the operation's format (`int32`, `uint32`, `int64` or
/// `uint64`, chosen by `conversion::usual_arithmetic_format`), as the
/// conversion table builds it. A narrow value widened into 32 bits is the
/// table's cast, whose word is its operand's (rule K8). A `_Bool` value,
/// which is no machine format yet (Stage 5 of `design/machine-integers.md`),
/// keeps its 0-or-1 word, extended at 64 bits. `None` for a value C does
/// not convert so: one `destination` neither contains nor reads modulo
/// 2^N as an unsigned type at least as wide, a 128-bit value, a pointer or
/// a float.
pub(in crate::kernel) fn promote_program_path_value(
    value: ProgramValue,
    destination: MachineIntegerType,
) -> Option<MachineTerm> {
    let value = value.numeric_value().clone();
    let to = destination.format();
    // Rule C1: a promoted `Bool` is its cast at the operation's format.
    if let ProgramValue::Bool(word) = value {
        return matches!(to.bits(), 32 | 64).then(|| MachineTerm::bool_word_as(destination, &word));
    }
    let source = MachineIntegerType::from_program_type(value.program_type())?;
    let from = source.format();
    if from.bits() > 64 || !(to.contains(from) || (!to.is_signed() && from.bits() <= to.bits())) {
        return None;
    }
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    Some(crate::kernel::machine_integer::conversion::convert_term(
        source,
        destination,
        term,
    ))
}

/// A C integer conversion between machine types of at most 64 bits, by the
/// conversion table. One that can change the value into a signed type, or
/// into an 8- or 16-bit one, is the narrowing [`narrow_integer`] builds,
/// where a specification's conversion owes its range; every other is the
/// table's term (σ, a widening, the low word of a 64-bit value). A widening
/// between two narrow formats reuses the word and is not built here.
fn convert_program_integer(
    value: ProgramValue,
    target: ProgramType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    let source = MachineIntegerType::from_program_type(value.program_type())?;
    let destination = MachineIntegerType::from_program_type(target)?;
    let (from, to) = (source.format(), destination.format());
    let sign_cast = from.bits() == 32 && to.bits() == 32;
    if !to.contains(from) && (to.bits() < 32 || (to.is_signed() && !sign_cast)) {
        return narrow_integer(value, target, conversion, obligations, assumptions);
    }
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    Some(
        destination.value_from_term(crate::kernel::machine_integer::conversion::convert_term(
            source,
            destination,
            term,
        )),
    )
}

/// The rule an integer conversion to a narrower type, or to the other
/// signedness of its width, follows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum IntegerConversion {
    /// C's conversion as GCC and Clang compile it, implicit or written: the
    /// value modulo 2^N of the destination width, owing nothing.
    Modular,
    /// A specification's conversion: it owes the destination's range in the
    /// source's own type, and within that range is the source's value. A
    /// constant outside the range is refused.
    Checked,
}

impl IntegerConversion {
    /// The conversion table's policy (`machine_integer::conversion`).
    pub(in crate::kernel) fn policy(
        self,
    ) -> crate::kernel::machine_integer::conversion::ConversionPolicy {
        use crate::kernel::machine_integer::conversion::ConversionPolicy;
        match self {
            Self::Modular => ConversionPolicy::Modular,
            Self::Checked => ConversionPolicy::Checked,
        }
    }
}

/// Converts a C value at an implicit conversion boundary, by C's rule.
pub(in crate::kernel) fn coerce_program_value_to_type(
    value: ProgramValue,
    target_type: ProgramType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    coerce_program_value_to_type_as(
        value,
        target_type,
        IntegerConversion::Modular,
        obligations,
        assumptions,
    )
}

pub(in crate::kernel) fn coerce_program_value_to_type_as(
    value: ProgramValue,
    target_type: ProgramType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    // Assignment and argument binding preserve complete, unchanged words.
    // Every other numeric conversion starts from a mathematical observation.
    if matches!(value, ProgramValue::PointerInteger(_)) && value.program_type() == target_type {
        return Some(value);
    }
    let value = value.numeric_value().clone();
    // Integer to `Bool` (Stage 5) is the test `value != 0`, exact at every
    // width: no value is reduced before it is tested.
    if target_type == ProgramType::Bool
        && matches!(
            value.program_type(),
            ProgramType::Int128 | ProgramType::UInt128
        )
    {
        return ConditionTerm::nonzero_test(&value).map(ProgramValue::of_bool);
    }
    if matches!(
        value.program_type(),
        ProgramType::Int128 | ProgramType::UInt128
    ) || matches!(target_type, ProgramType::Int128 | ProgramType::UInt128)
    {
        let destination = MachineIntegerType::from_program_type(target_type)?;
        // Rule C1: a `Bool` widened to 128 bits is its cast, 1 or 0.
        if let ProgramValue::Bool(word) = &value {
            let destination = MachineIntegerType::from_program_type(target_type)?;
            return ProgramValue::from_bitvector_term(
                target_type,
                MachineTerm::bool_word_as(destination, word),
            );
        }
        let source = MachineIntegerType::from_program_type(value.program_type())?;
        // C's conversion is modulo 2^N for a signed destination too; a
        // specification's owes the signed range. An unsigned destination is
        // modulo 2^N under both (the conversion table's policy column).
        if crate::kernel::machine_integer::conversion::lower(
            source,
            destination,
            conversion.policy(),
        )
        .owes_range
        {
            let observed =
                IntegerTerm::from_machine(source, program_value_bitvector_term(&value)?)?;
            let (min, max) = destination.format().bounds();
            for (condition, context) in [
                (
                    ConditionTerm::IntegerGreaterEqual(
                        observed.clone().into(),
                        IntegerTerm::constant(min).into(),
                    ),
                    "signed narrowing lower bound",
                ),
                (
                    ConditionTerm::IntegerLessEqual(
                        observed.into(),
                        IntegerTerm::constant(max).into(),
                    ),
                    "signed narrowing upper bound",
                ),
            ] {
                add_narrowing_bound_obligation(obligations, assumptions, condition, context)?;
            }
        }
        return crate::kernel::machine_integer::conversion::convert_value(value, destination);
    }
    if let Some(value) = coerce_program_null_pointer_constant(value.clone(), target_type) {
        return Some(value);
    }

    if matches!(target_type, ProgramType::FunctionPointer(_))
        && let ProgramValue::Pointer(pointer) = &value
        && pointer.program_type() == target_type
    {
        return Some(value);
    }

    // A direct function address starts with the intentionally untyped
    // unspecified signature marker. Call arguments retag it from the declared
    // parameter type before binding; typed stores need the same destination
    // context so a callback field can be initialized without weakening
    // already-typed function-pointer compatibility checks.
    if let (ProgramType::FunctionPointer(signature), ProgramValue::Pointer(pointer)) =
        (target_type, &value)
        && pointer.base.is_function()
        && pointer.program_type() == ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED)
    {
        return Some(ProgramValue::typed_pointer(
            pointer.address().clone(),
            ProgramType::FunctionPointer(signature),
        ));
    }

    match (target_type, value) {
        (ProgramType::Bool, ProgramValue::Bool(value)) => Some(ProgramValue::Bool(value)),
        // Integer to `Bool` (Stage 5): the test `value != 0`, or a non-null
        // test for a pointer.
        (
            ProgramType::Bool,
            value @ (crate::kernel::integer64_c_value!(_) | ProgramValue::Pointer(_)),
        ) => ConditionTerm::nonzero_test(&value).map(ProgramValue::of_bool),
        // Rule C1: a `Bool` read as an integer is its cast at the target's
        // format, 1 when it holds and 0 otherwise.
        (
            target @ (ProgramType::Int8
            | ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64),
            ProgramValue::Bool(word),
        ) => ProgramValue::from_bitvector_term(
            target,
            MachineTerm::bool_word_as(MachineIntegerType::from_program_type(target)?, &word),
        ),
        // C's widening between narrow formats is a conversion node of the
        // destination's width, as the source writes it.
        (ProgramType::Int16, ProgramValue::Int8(value)) => {
            Some(ProgramValue::Int16(MachineTerm::machine_integer_cast(
                MachineIntegerType::Int8,
                MachineIntegerType::Int16,
                value,
            )))
        }
        (ProgramType::Int16, ProgramValue::UInt8(value)) => {
            Some(ProgramValue::Int16(MachineTerm::machine_integer_cast(
                MachineIntegerType::UInt8,
                MachineIntegerType::Int16,
                value,
            )))
        }
        (ProgramType::UInt16, ProgramValue::UInt8(value)) => {
            Some(ProgramValue::UInt16(MachineTerm::machine_integer_cast(
                MachineIntegerType::UInt8,
                MachineIntegerType::UInt16,
                value,
            )))
        }
        (
            target @ (ProgramType::Int8
            | ProgramType::UInt8
            | ProgramType::Int16
            | ProgramType::UInt16
            | ProgramType::Int32
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64),
            value @ crate::kernel::integer64_c_value!(_),
        ) => convert_program_integer(value, target, conversion, obligations, assumptions),
        (ProgramType::Float32, ProgramValue::Float32(value)) => Some(ProgramValue::Float32(value)),
        (ProgramType::Float32, ProgramValue::Float64(value)) => {
            let operand = value
                .float64_as_const()
                .map(MachineTerm::uint64_constant)
                .unwrap_or(value);
            let converted = MachineTerm::opaque_conversion("c_float64_to_float32", operand);
            Some(ProgramValue::Float32(converted))
        }
        (ProgramType::Float64, ProgramValue::Float64(value)) => Some(ProgramValue::Float64(value)),
        (ProgramType::Float64, ProgramValue::Float32(value)) => {
            let operand = value
                .float32_as_const()
                .map(MachineTerm::constant)
                .unwrap_or(value);
            let converted = MachineTerm::opaque_conversion("c_float32_to_float64", operand);
            Some(ProgramValue::Float64(converted))
        }
        (
            target @ (ProgramType::Float32 | ProgramType::Float64),
            value @ (crate::kernel::integer64_c_value!(_)),
        ) => integer_to_float_value(value, target),
        (
            target @ (ProgramType::Int8
            | ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64),
            ProgramValue::Float32(value),
        ) => {
            if let Some(bits) = value.float32_as_const() {
                float32_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    ProgramType::Float32,
                    target,
                    obligations,
                    assumptions,
                )
            }
        }
        (
            target @ (ProgramType::Int8
            | ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64),
            ProgramValue::Float64(value),
        ) => {
            if let Some(bits) = value.float64_as_const() {
                float64_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    ProgramType::Float64,
                    target,
                    obligations,
                    assumptions,
                )
            }
        }
        _ => None,
    }
}

/// Converts an integer into a narrower type, or between the two
/// signednesses of one width.
///
/// C's conversion ([`IntegerConversion::Modular`]) is what GCC and Clang do
/// on every target Click models: the destination's value congruent to the
/// source's modulo 2^N (C11 6.3.1.3p2 for an unsigned destination, GCC's
/// documented implementation-defined choice for a signed one). It owes
/// nothing. Into a one- or two-byte type the result is the typed conversion
/// node, never a re-tagged carrier, so a value outside the destination range
/// cannot masquerade as one inside it. Inside that range the node denotes
/// its operand: the reasoning layer replaces it by the operand's carrier
/// once the context proves the range (`narrowed_cast_identity`), in search
/// and checker alike. A byte converted from an unsigned byte is the
/// one-byte-one-name signed read of that byte, `MachineTerm::signed_byte`.
/// Into `int32` the low word already is the value modulo 2^32, and into
/// `int64` the same 64 bits read as signed.
///
/// A specification's conversion ([`IntegerConversion::Checked`]) files the
/// same range conditions as obligations. Its result is the same conversion
/// node, and its caller files the node's identity with its operand, which
/// holds exactly where those obligations do.
fn narrow_integer(
    value: ProgramValue,
    target: ProgramType,
    policy: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    let source = MachineIntegerType::from_program_type(value.program_type())?;
    let destination = MachineIntegerType::from_program_type(target)?;
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    use crate::kernel::machine_integer::conversion;
    // The conversion table says what this conversion owes; its term is the
    // table's whatever the policy.
    let checked = conversion::lower(source, destination, policy.policy()).owes_range;
    match destination {
        MachineIntegerType::Int32 => {
            if checked {
                let bounds = if source == MachineIntegerType::UInt64 {
                    vec![(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::UInt64,
                            relation: CompareRelation::LessEqual,
                            left: term.clone().into(),
                            right: MachineTerm::uint64_constant(i32::MAX as u64).into(),
                        },
                        "int32 narrowing upper bound",
                    )]
                } else {
                    vec![
                        (
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int64,
                                relation: CompareRelation::GreaterEqual,
                                left: term.clone().into(),
                                right: MachineTerm::int64_constant(i64::from(i32::MIN)).into(),
                            },
                            "int32 narrowing lower bound",
                        ),
                        (
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int64,
                                relation: CompareRelation::LessEqual,
                                left: term.clone().into(),
                                right: MachineTerm::int64_constant(i64::from(i32::MAX)).into(),
                            },
                            "int32 narrowing upper bound",
                        ),
                    ]
                };
                for (condition, context) in bounds {
                    add_narrowing_bound_obligation(obligations, assumptions, condition, context)?;
                }
            }
            Some(ProgramValue::Int32(conversion::convert_term(
                source,
                destination,
                term,
            )))
        }
        MachineIntegerType::Int64 => {
            if checked {
                add_narrowing_bound_obligation(
                    obligations,
                    assumptions,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessEqual,
                        left: term.clone().into(),
                        right: MachineTerm::uint64_constant(i64::MAX as u64).into(),
                    },
                    "int64 narrowing upper bound",
                )?;
            }
            Some(ProgramValue::Int64(conversion::convert_term(
                source,
                destination,
                term,
            )))
        }
        _ if source == destination => Some(destination.value_from_term(term)),
        // The node is the same whatever the context knows, so a smart search
        // and the checked trace of its steps produce one term; the identity
        // inside the range is reasoning (`narrowed_cast_identity`), never a
        // context-dependent choice of representation here.
        _ if !checked => {
            Some(destination.value_from_term(conversion::convert_term(source, destination, term)))
        }
        _ => {
            let (bounds, _) =
                crate::kernel::assumptions::narrowed_cast_identity(&term, source, destination)?;
            for bound in bounds {
                let condition = bound.conditions.into_iter().next()?;
                add_narrowing_bound_obligation(
                    obligations,
                    assumptions,
                    condition,
                    narrowing_context(destination, bound.lower),
                )?;
            }
            // The result is the conversion node, the canonical carrier of the
            // destination. Inside the range the obligations above require,
            // it denotes its operand; the caller files that identity
            // (`checked_narrowing_identity`).
            Some(destination.value_from_term(conversion::convert_term(source, destination, term)))
        }
    }
}

/// The identity `to_integer(conv(v)) == to_integer(v)` of a checked
/// narrowing whose result `converted` is the conversion node of `source`,
/// and, for an operand of at most 32 bits, the word identity `conv(w) == w`.
///
/// A checked narrowing files its operand's destination-range bounds as the
/// path's obligations (`narrow_integer`), and inside that range the modular
/// conversion leaves the value unchanged. So the identity holds on every
/// path where the obligations do, which is every path that carries them;
/// it is a consequence of the step, as a narrow value's range is. The node
/// is the destination's canonical carrier, the sign or zero extension of
/// its value, and an operand word of at most 32 bits is likewise its own
/// value's extension, so inside the range the two words are equal. That is
/// the form a comparison of words takes, which a Rust narrow result's `==`
/// lowers to. A conversion that cannot change the value, or a folded
/// constant, has no node and files nothing.
pub(in crate::kernel) fn checked_narrowing_identity(
    source: &ProgramValue,
    converted: &ProgramValue,
) -> Vec<Proposition> {
    checked_narrowing_identity_readings(source, converted).unwrap_or_default()
}

fn checked_narrowing_identity_readings(
    source: &ProgramValue,
    converted: &ProgramValue,
) -> Option<Vec<Proposition>> {
    let source_type = MachineIntegerType::from_program_type(source.program_type())?;
    let operand = match source.numeric_value() {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    let converted = converted_term(converted)?;
    let MachineTerm::Cast {
        spelling: MachineCastSpelling::Generic,
        value,
        from: cast_source,
        to: destination,
    } = converted
    else {
        return None;
    };
    // The conversion names the operand as written, σ included.
    if *cast_source != source_type || value.as_ref() != operand {
        return None;
    }

    let observed = IntegerTerm::from_machine(*destination, converted.clone())?;
    let original = IntegerTerm::from_machine(source_type, operand.clone())?;
    let mut identities = vec![Proposition::condition_is(
        ConditionTerm::integer_equal(observed, original),
        true,
    )];
    if source_type.format().bits() <= 32 {
        // The narrow result is a value of its own width; its widening is the
        // operand's word, itself widened when the operand is narrow too.
        let word = |ty: MachineIntegerType, term: &MachineTerm| {
            if ty.format().bits() < 32 {
                MachineTerm::machine_integer_cast(ty, MachineIntegerType::Int32, term.clone())
            } else {
                term.clone()
            }
        };
        identities.push(Proposition::condition_is(
            ConditionTerm::equal(word(*destination, converted), word(source_type, operand)),
            true,
        ));
    }
    Some(identities)
}

fn converted_term(value: &ProgramValue) -> Option<&MachineTerm> {
    match value {
        ProgramValue::Int8(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::Int16(term)
        | ProgramValue::UInt16(term) => Some(term),
        _ => None,
    }
}

/// Files one bound of a checked integer narrowing conversion as the
/// obligation the conversion owes.
///
/// A bound the facts refute is filed as well: the conversion then yields its
/// value under an obligation no proof discharges, and the proof reports that
/// bound against the facts that refute it. Narrowing sites construct the
/// comparison without constant folding, so a failed bound still spells its
/// value and endpoint rather than just `false`; constants owe the same
/// obligation.
fn add_narrowing_bound_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    context: &'static str,
) -> Option<()> {
    if add_proof_obligation_with_context(
        obligations,
        assumptions,
        Proposition::condition_is(condition.clone(), true),
        Some(context),
    )
    .is_some()
    {
        return Some(());
    }
    obligations.push(ProofObligation::condition(condition, true).with_context(context));
    Some(())
}

fn narrowing_context(destination: MachineIntegerType, lower: bool) -> &'static str {
    match (destination, lower) {
        (MachineIntegerType::UInt8, true) => "uint8 narrowing lower bound",
        (MachineIntegerType::UInt8, false) => "uint8 narrowing upper bound",
        (MachineIntegerType::Int8, true) => "int8 narrowing lower bound",
        (MachineIntegerType::Int8, false) => "int8 narrowing upper bound",
        (MachineIntegerType::Int16, true) => "int16 narrowing lower bound",
        (MachineIntegerType::Int16, false) => "int16 narrowing upper bound",
        (MachineIntegerType::UInt16, true) => "uint16 narrowing lower bound",
        (MachineIntegerType::UInt16, false) => "uint16 narrowing upper bound",
        _ => "integer narrowing bound",
    }
}

pub(in crate::kernel) fn cast_program_value_to_type(
    value: ProgramValue,
    target_type: ProgramType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Result<ProgramValue, RuntimeError> {
    cast_program_value_to_type_with_integer_origin(
        value,
        target_type,
        conversion,
        obligations,
        assumptions,
        None,
    )
}

/// A pointer conversion, written or implicit. C11 6.3.2.3p7 gives one
/// conversion a meaning of its own: converting to a character pointer forms
/// a view of the object's bytes. That view spans the allocation (TS 6010's
/// provenance granularity), so it is not bounded by the member the operand
/// was formed from. A conversion between character types keeps the existing
/// view, and every other conversion, including to `void *`, keeps the value
/// (`design/pointer-model.md`).
pub(in crate::kernel) fn cast_pointer_value(pointer: Pointer, target_type: ProgramType) -> Pointer {
    let forms_byte_view =
        is_character_pointer(target_type) && !is_character_pointer(pointer.program_type());
    let pointer = pointer.with_type(target_type);
    if forms_byte_view {
        pointer.with_root_bounds()
    } else {
        pointer
    }
}

/// A pointer to a structure's initial member, converted to the structure's
/// type, points to the structure (C11 6.7.2.1p15). When the operand's array
/// object is a member starting at its address and narrower than the struct,
/// the result's array object is the `size` bytes of the struct there. An
/// operand whose bounds are not yet known keeps them: they remain the opaque
/// domain the bounds evidence of each access decides. Whether such a struct exists
/// is the effective-type question each access through the result already
/// asks (C11 6.5p7). Any other operand keeps its value: a pointer inside a
/// member is not an initial member's, and an array object that already
/// covers the struct, such as an allocation used as an array of it, is not
/// narrowed.
fn struct_view_of_initial_member(pointer: Pointer, size: u32) -> Pointer {
    if pointer.is_null() || pointer.address().base.is_function() {
        return pointer;
    }
    match pointer.bounds() {
        Some(bounds)
            if bounds.start == *pointer.address()
                && bounds.constant_width().is_some_and(|width| width < size) =>
        {
            let start = pointer.address().clone();
            pointer.with_bounds(Some(SubobjectBounds::constant(start, size)))
        }
        _ => pointer,
    }
}

fn is_character_pointer(program_type: ProgramType) -> bool {
    matches!(
        program_type,
        ProgramType::UInt8Pointer | ProgramType::Int8Pointer
    )
}

fn cast_program_value_to_type_with_integer_origin(
    value: ProgramValue,
    target_type: ProgramType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    integer_pointer_origin: Option<Address>,
) -> Result<ProgramValue, RuntimeError> {
    if target_type.is_pointer() {
        match value {
            ProgramValue::PointerInteger(record)
                if !matches!(target_type, ProgramType::FunctionPointer(_)) =>
            {
                // Numeric observations cannot choose the representation carrier.
                // A checked tagged value must have its tag removed before use.
                let pointer = match record.kind {
                    PointerIntegerKind::Exact => *record.pointer,
                    PointerIntegerKind::Word { changed_bits } => {
                        if changed_bits != 0 {
                            return Err(RuntimeError::PointerConversion(
                                "integer-to-pointer cast requires modified tag bits cleared".into(),
                            ));
                        }
                        let bits =
                            crate::kernel::spec::program_value_bitvector_term(&record.numeric)
                                .ok_or(RuntimeError::TypeMismatch)?;
                        // A logical cast must name the same value before its
                        // own relationship is assumed. Numeric address choices
                        // belong to execution, never to this carrier's name.
                        record
                            .pointer
                            .with_address(Address::from_integer_address(bits))
                    }
                    PointerIntegerKind::Tagged => {
                        let bits =
                            crate::kernel::spec::program_value_bitvector_term(&record.numeric)
                                .ok_or(RuntimeError::TypeMismatch)?;
                        let recovered = super::pointer_tags::cast_tagged_address_to_pointer(
                            &bits,
                            assumptions,
                            obligations,
                            target_type,
                        )
                        .map_err(RuntimeError::PointerConversion)?;
                        if recovered.as_ref().map(Pointer::address)
                            != Some(record.pointer.address())
                        {
                            return Err(RuntimeError::PointerConversion(
                                "integer-to-pointer cast requires the original pointer with its tag cleared".into(),
                            ));
                        }
                        *record.pointer
                    }
                };
                return Ok(ProgramValue::Pointer(pointer.with_type(target_type)));
            }
            ProgramValue::Pointer(pointer) => {
                return Ok(ProgramValue::Pointer(cast_pointer_value(
                    pointer,
                    target_type,
                )));
            }
            // An address without a complete representation record reconstructs
            // an opaque provenance. Numeric facts cannot supply pointer bounds.
            ProgramValue::UInt64(term) | ProgramValue::Int64(term)
                if !matches!(target_type, ProgramType::FunctionPointer(_)) =>
            {
                if term.uint64_as_const() == Some(0)
                    || assumptions.decide(&ConditionTerm::uint64_equal(
                        term.clone(),
                        MachineTerm::uint64_constant(0),
                    )) == Some(true)
                {
                    return Ok(ProgramValue::typed_pointer(Address::null(), target_type));
                }
                // Numeric tag equations recover coordinates and source object class,
                // never the original provenance or bounds.
                return match super::pointer_tags::cast_tagged_address_to_pointer(
                    &term, assumptions, obligations, target_type,
                ) {
                    Ok(Some(pointer)) if pointer.address() == &Address::null() => Ok(ProgramValue::Pointer(pointer)),
                    Ok(Some(pointer)) => {
                        let origin = integer_pointer_origin.ok_or_else(|| RuntimeError::PointerConversion(
                            "integer-to-pointer cast requires a complete representation or a fresh cast identity".into(),
                        ))?;
                        Ok(ProgramValue::Pointer(Pointer::new(origin, target_type)
                            .with_address(pointer.address().clone())
                            .with_declared_object_class(pointer.object_class())))
                    }
                    Ok(None) => Err(RuntimeError::PointerConversion(
                        "integer-to-pointer cast requires an unchanged pointer representation, a recorded address, or zero".to_string(),
                    )),
                    Err(message) => Err(RuntimeError::PointerConversion(message)),
                };
            }
            value => {
                return coerce_program_value_to_type_as(
                    value,
                    target_type,
                    conversion,
                    obligations,
                    assumptions,
                )
                .ok_or(RuntimeError::TypeMismatch);
            }
        }
    }
    if let ProgramValue::Pointer(pointer) = &value {
        // Pointer-to-integer conversion under LP64: the integer is the
        // pointer's address term, which keeps the exact source pointer. Null
        // is the integer zero; function addresses are not modeled.
        if !matches!(target_type, ProgramType::UInt64 | ProgramType::Int64) {
            return Err(RuntimeError::PointerConversion(
                "pointer-to-integer cast requires a 64-bit integer type under the LP64 \
                 profile; a narrower integer cannot hold a pointer"
                    .to_string(),
            ));
        }
        if pointer.base.is_function()
            || matches!(pointer.program_type(), ProgramType::FunctionPointer(_))
        {
            return Err(RuntimeError::PointerConversion(
                "function addresses do not convert to integers".to_string(),
            ));
        }
        let address =
            MachineTerm::object_pointer_address(pointer.address().clone(), pointer.object_class());
        let numeric = match target_type {
            ProgramType::UInt64 => ProgramValue::UInt64(address),
            _ => ProgramValue::Int64(address),
        };
        return Ok(ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(numeric),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        }));
    }
    coerce_program_value_to_type_as(value, target_type, conversion, obligations, assumptions)
        .ok_or(RuntimeError::TypeMismatch)
}

/// The undefined behavior of operating on `value` when it is a pointer into
/// an allocation the current state has freed.
///
/// C11 6.2.4p2 makes a pointer's value indeterminate when its pointee's
/// lifetime ends, and Annex J.2 lists using such a value as undefined. Reading
/// the pointer out of a cell, storing it, or passing or returning it as a
/// pointer is not such a use in Click's model; comparing it (with anything,
/// null included), subtracting or offsetting it, testing its truth, or
/// converting it to an integer or `_Bool` (by a cast, or implicitly at an
/// assignment, a `return`, or a call argument) is. The evidence is positive: the pointer's own block holds an
/// exact deallocated base or an offset into one (see
/// [`SymbolicMemory::deallocated_heap_allocation_holding`]). A pointer whose block
/// is neither shown freed nor shown live keeps its ordinary meaning.
pub(in crate::kernel) fn freed_pointer_use(
    state: &ExecutionState,
    value: &ProgramValue,
    assumptions: &PureFactContext,
) -> Option<UndefinedBehavior> {
    let ProgramValue::Pointer(pointer) = value else {
        return None;
    };
    if pointer.is_null() || pointer.base.is_function() {
        return None;
    }
    state
        .memory()
        .deallocated_heap_allocation_holding(pointer.address(), assumptions)?;
    Some(UndefinedBehavior::FreedPointerUse)
}

/// Refuses each value path whose value is a pointer into a freed allocation;
/// see [`freed_pointer_use`]. Every other path is kept as it is.
pub(in crate::kernel) fn refuse_freed_pointer_value_paths(
    state: &ExecutionState,
    paths: Vec<ExpressionPath>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    if state.memory().heap_has_no_deallocations() {
        return paths;
    }
    paths
        .into_iter()
        .map(|path| match &path.outcome {
            ExpressionOutcome::Value(value) => match freed_pointer_use(state, value, assumptions) {
                Some(undefined_behavior) => ExpressionPath {
                    outcome: ExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    ..path
                },
                None => path,
            },
            _ => path,
        })
        .collect()
}

/// Evaluates a controlling expression whose value will be tested for truth
/// (`if`, loops, `?:`, `!`, `&&`, `||`, `assert`). Testing a freed pointer's
/// truth compares it with null, so such a value is refused here; see
/// [`freed_pointer_use`].
pub(in crate::kernel) fn evaluate_program_condition_paths(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let paths = evaluate_program_expression_paths(state, condition, assumptions, budget)?;
    Ok(refuse_freed_pointer_value_paths(state, paths, assumptions))
}

pub(in crate::kernel) fn coerce_program_null_pointer_constant(
    value: ProgramValue,
    target_type: ProgramType,
) -> Option<ProgramValue> {
    if target_type.accepts(&value) {
        return Some(match value {
            ProgramValue::Pointer(pointer) => ProgramValue::Pointer(pointer.with_type(target_type)),
            value => value,
        });
    }
    match (target_type, value) {
        (target_type, ProgramValue::Int32(bits32_constant!(0))) if target_type.is_pointer() => {
            Some(ProgramValue::typed_pointer(Address::null(), target_type))
        }
        _ => None,
    }
}

/// Explicit compatibility boundary for consumers that still require native values.
pub(in crate::kernel) fn evaluate_program_expression_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    Ok(
        evaluate_expression_value_paths(state, expression, assumptions, budget)?
            .into_iter()
            .map(|path| path.map_value(crate::kernel::execution_value::ExecutionValue::into_native))
            .collect(),
    )
}

pub(super) fn evaluate_native_expression_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    budget.consume_expression_step()?;
    let mut paths = match expression {
        ProgramExpression::Value(ProgramValue::Void) => vec![ExpressionPath {
            outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        ProgramExpression::Value(value) => {
            // A value the kernel substituted into an expression is introduced
            // to it here, as a read introduces a stored one.
            let mut facts = ExecutionFacts::new();
            add_narrow_integer_range_execution_pure_facts(&mut facts, assumptions, value);
            vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(value.clone()),
                facts,
                obligations: Vec::new(),
            }]
        }
        ProgramExpression::Variable(name)
            if state.locals.binding(name).is_none()
                && name
                    .static_id()
                    .and_then(|id| id.metadata())
                    .is_some_and(|metadata| {
                        metadata.aggregate || metadata.array_shape.is_some()
                    }) =>
        {
            let metadata = name
                .static_id()
                .and_then(|id| id.metadata())
                .expect("prepared static object");
            let pointer_type = if metadata.aggregate {
                ProgramType::UInt8Pointer
            } else {
                metadata
                    .program_type
                    .array_element_type()
                    .and_then(ProgramType::pointer_to)
                    .expect("static scalar array element has a pointer type")
            };
            vec![ExpressionPath {
                outcome: ExpressionOutcome::Value(
                    ProgramValue::typed_pointer_with_pointee_constant(
                        SymbolicMemory::global_pointer(name),
                        pointer_type,
                        metadata.constant,
                    ),
                ),
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }]
        }
        ProgramExpression::Variable(name)
            if state.locals.is_array_object(name) || state.locals.is_aggregate_object(name) =>
        {
            let pointer = state
                .locals
                .slot(name)
                .expect("array binding must carry a stack slot")
                .clone();
            let pointee_constant = match state.locals.binding(name) {
                Some(LocalBinding::ArrayObject { constant, .. })
                | Some(LocalBinding::AggregateObject { constant, .. }) => *constant,
                _ => false,
            };
            vec![ExpressionPath {
                outcome: if state.memory.has_block(&pointer.base) {
                    ExpressionOutcome::Value(ProgramValue::typed_pointer_with_pointee_constant(
                        pointer,
                        if state.locals.is_aggregate_object(name) {
                            ProgramType::UInt8Pointer
                        } else {
                            state
                                .locals
                                .object_type(name)
                                .and_then(ProgramType::pointer_to)
                                .unwrap_or(ProgramType::Int32Pointer)
                        },
                        pointee_constant,
                    ))
                } else {
                    ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(name.to_string()))
                },
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }]
        }
        ProgramExpression::Variable(_) => {
            read_program_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
        // The term this statement's own call step returned.
        ProgramExpression::StringLiteral(identity) => vec![ExpressionPath {
            outcome: state
                .literal_values
                .get(identity)
                .map(|value| ExpressionOutcome::Value(value.native().into_owned()))
                .unwrap_or_else(|| {
                    ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(
                        identity.to_string(),
                    ))
                }),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        ProgramExpression::StepResult { step, .. } => vec![ExpressionPath {
            outcome: match state
                .step_results
                .as_ref()
                .and_then(|results| results.get(step))
            {
                Some(value) => ExpressionOutcome::Value(value.native().into_owned()),
                None => ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(format!(
                    "the result of step {step}, read before the step ran"
                ))),
            },
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        ProgramExpression::FunctionAddress(name) => vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::typed_pointer(
                Address::function(name.clone()),
                ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
            )),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        ProgramExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct: _,
            pointee_struct_size,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => evaluate_program_cast_paths(
            state,
            expression,
            *target_type,
            *integer_mode,
            *pointee_struct_size,
            *pointee_volatile,
            *pointee_constant,
            *explicit_qualification,
            assumptions,
            budget,
        )?,
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => evaluate_program_conditional_paths(
            state,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        )?,
        ProgramExpression::Negate(expression) => {
            evaluate_program_negate_paths(state, expression, assumptions, budget)?
        }
        ProgramExpression::FloatNegate(expression) => {
            evaluate_program_float_negate_paths(state, expression, assumptions, budget)?
        }
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => evaluate_program_enum_construct_paths(
            state,
            *enum_type,
            variant,
            fields,
            assumptions,
            budget,
        )?
        .into_iter()
        .map(ExpressionPath::into_native)
        .collect(),
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => evaluate_program_enum_field_paths(state, value, variant, *index, assumptions, budget)?
            .into_iter()
            .map(ExpressionPath::into_native)
            .collect(),
        ProgramExpression::EnumIs { value, variant } => {
            evaluate_program_enum_is_paths(state, value, variant, assumptions, budget)?
        }
        ProgramExpression::FloatClassification {
            expression,
            classification,
        } => evaluate_program_float_classification_paths(
            state,
            expression,
            *classification,
            assumptions,
            budget,
        )?,
        ProgramExpression::AddressOf(target) => {
            address_of_lvalue_paths(state, target, assumptions, budget)?
        }
        ProgramExpression::CheckedObjectAddress(target) => {
            let width = program_expression_lvalue_type(state, target)
                .map(|ty| ty.byte_width())
                .filter(|width| *width > 0);
            let mut paths = address_of_lvalue_paths(state, target, assumptions, budget)?;
            for path in &mut paths {
                if let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &path.outcome {
                    let Some(width) = width else {
                        path.outcome = ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch);
                        continue;
                    };
                    let outside_known_block = match (
                        pointer.address().offset.as_const(),
                        state
                            .memory()
                            .block_size(&pointer.address().base)
                            .and_then(|size| size.as_const()),
                    ) {
                        (Some(offset), Some(size)) => {
                            offset < 0
                                || offset
                                    .checked_add(i64::from(width))
                                    .is_none_or(|end| end > i64::from(size))
                        }
                        _ => false,
                    };
                    if pointer.address().is_in_null_block()
                        || outside_known_block
                        || state.memory().is_ended_local_address(pointer.address())
                        || state
                            .memory()
                            .is_deallocated_heap_address(pointer.address(), assumptions)
                    {
                        path.outcome =
                            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory);
                        continue;
                    }
                    // A wide range states no loadable fact, which counts
                    // bytes in 32 bits. A held range that permits reading
                    // the whole referent is the same evidence of live
                    // storage, and is what a load of it would rest on.
                    if !assumptions.proves_memory_loadable(
                        state.memory(),
                        pointer.address(),
                        &MachineTerm::constant(width),
                    ) && state.resources().permits_memory_read(
                        pointer.address(),
                        width,
                        assumptions,
                    ) {
                        continue;
                    }
                    let _ = add_proof_obligation_with_context(
                        &mut path.obligations,
                        assumptions,
                        Proposition::MemoryLoadable {
                            memory: state.memory().clone(),
                            base: pointer.address().clone(),
                            bytes: (MachineTerm::constant(width)).into(),
                            wide: false,
                        },
                        Some("reference binding requires live storage for the complete referent"),
                    );
                }
            }
            paths
        }
        ProgramExpression::Subobject { pointer, width } => {
            evaluate_program_expression_paths(state, pointer, assumptions, budget)?
                .into_iter()
                .flat_map(|path| match path.outcome {
                    ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => subobject_paths(
                        pointer,
                        *width,
                        path.facts,
                        path.obligations,
                        assumptions,
                        state.resources(),
                    ),
                    ExpressionOutcome::Value(_) => vec![ExpressionPath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    outcome => vec![ExpressionPath {
                        outcome,
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                })
                .collect()
        }
        ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
            evaluate_program_expression_paths(state, pointer, assumptions, budget)?
                .into_iter()
                .flat_map(|path| match path.outcome {
                    ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => {
                        pointer_offset_by_bytes_paths(
                            state,
                            pointer,
                            *bytes,
                            path.facts,
                            path.obligations,
                            assumptions,
                        )
                    }
                    ExpressionOutcome::Value(_) => vec![ExpressionPath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    ExpressionOutcome::UndefinedBehavior(error) => vec![ExpressionPath {
                        outcome: ExpressionOutcome::UndefinedBehavior(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    ExpressionOutcome::RuntimeError(error) => vec![ExpressionPath {
                        outcome: ExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                })
                .collect()
        }
        ProgramExpression::LessThan(left, right) => evaluate_program_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            ComparisonOperator::LessThan,
        )?,
        ProgramExpression::LessEqual(left, right) => evaluate_program_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            ComparisonOperator::LessEqual,
        )?,
        ProgramExpression::GreaterThan(left, right) => evaluate_program_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            ComparisonOperator::GreaterThan,
        )?,
        ProgramExpression::GreaterEqual(left, right) => evaluate_program_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            ComparisonOperator::GreaterEqual,
        )?,
        ProgramExpression::Equal(left, right) => {
            evaluate_program_equal_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::NotEqual(left, right) => {
            evaluate_program_not_equal_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::Not(expression) => {
            evaluate_program_not_paths(state, expression, assumptions, budget)?
        }
        ProgramExpression::And(left, right) => {
            evaluate_program_logical_and_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::Or(left, right) => {
            evaluate_program_logical_or_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::Add(left, right) => {
            evaluate_program_add_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::Subtract(left, right) => {
            evaluate_program_subtract_paths(state, left, right, assumptions, budget)?
        }
        ProgramExpression::Multiply(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::Divide(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::Remainder(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::ShiftLeft(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::RustShiftLeft(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_rust_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::ShiftRight(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::RustShiftRight(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_rust_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        ProgramExpression::BitwiseAnd(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    BitwiseOperation::And,
                )
            },
        )?,
        ProgramExpression::BitwiseOr(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    BitwiseOperation::Or,
                )
            },
        )?,
        ProgramExpression::BitwiseXor(left, right) => evaluate_program_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_program_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    BitwiseOperation::Xor,
                )
            },
        )?,
        ProgramExpression::BitwiseNot(expression) => {
            let mut paths = Vec::new();
            for path in evaluate_program_expression_paths(state, expression, assumptions, budget)? {
                match path.outcome {
                    ExpressionOutcome::Value(value) => paths.extend(apply_program_bitwise_not(
                        value,
                        path.facts,
                        path.obligations,
                    )),
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(ExpressionPath {
                            outcome: ExpressionOutcome::UndefinedBehavior(undefined_behavior),
                            facts: path.facts,
                            obligations: path.obligations,
                        })
                    }
                    ExpressionOutcome::RuntimeError(error) => paths.push(ExpressionPath {
                        outcome: ExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }),
                }
            }
            paths
        }
        // An inline array field is an lvalue whose value is not represented by
        // ProgramValue. In an expression context it undergoes C's array-to-pointer
        // conversion, so evaluate the field's address rather than attempting
        // to load an aggregate value.
        ProgramExpression::TypedLoad {
            pointer,
            value_type:
                ProgramType::Int32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::Int8Array(_)
                | ProgramType::Int16Array(_)
                | ProgramType::UInt16Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_)
                | ProgramType::Float32Array(_)
                | ProgramType::Float64Array(_)
                | ProgramType::PointerArray(_, _),
            ..
        } => {
            let target_type = program_expression_pointee_type(state, expression)
                .and_then(ProgramType::pointer_to)
                .expect("supported array field has an element pointer type");
            let mut paths = evaluate_program_expression_paths(state, pointer, assumptions, budget)?;
            for path in &mut paths {
                if let ExpressionOutcome::Value(value) = &mut path.outcome {
                    *value = value.clone().retag_pointer(target_type);
                }
            }
            paths
        }
        ProgramExpression::Load(_)
        | ProgramExpression::TypedLoad { .. }
        | ProgramExpression::Index(_, _) => {
            read_program_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
    };
    // A wide wrapper cannot reinterpret a legacy word or arithmetic node.
    // Inspect the root only, including values read from locals or call results.
    for path in &mut paths {
        if let ExpressionOutcome::Value(
            value @ (ProgramValue::Int128(_) | ProgramValue::UInt128(_)),
        ) = &path.outcome
            && !value.program_type().accepts(value)
        {
            path.outcome = ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch);
        }
    }
    budget.check_path_width(paths.len())?;
    for path in &paths {
        if let ExpressionOutcome::Value(value) = &path.outcome {
            crate::kernel::debug_assert_widths(
                "an evaluated expression",
                || crate::kernel::value_mismatch(value),
                value,
            );
        }
    }
    Ok(paths)
}

/// A Rust `Bool` value (Stage 5, decision D5): `expression`, a comparison,
/// `!` or connective, evaluated as the `Bool` it tests, with no path split
/// ([`ConditionValueScope`]). Its operands are evaluated as usual.
fn evaluate_bool_value_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let paths = {
        let _condition_values = ConditionValueScope::enter();
        evaluate_program_expression_paths(state, expression, assumptions, budget)?
    };
    // A Rust comparison whose operands are written without a cast compares
    // values of one type; at 8 or 16 bits it is native at that type, so the
    // promoted comparison the evaluator built is read back as it (rule K8).
    // An operand written with `as` keeps the comparison at the cast's type.
    let native_comparison = match expression {
        ProgramExpression::Equal(left, right)
        | ProgramExpression::NotEqual(left, right)
        | ProgramExpression::LessThan(left, right)
        | ProgramExpression::LessEqual(left, right)
        | ProgramExpression::GreaterThan(left, right)
        | ProgramExpression::GreaterEqual(left, right) => {
            !matches!(left.as_ref(), ProgramExpression::Cast { .. })
                && !matches!(right.as_ref(), ProgramExpression::Cast { .. })
        }
        _ => false,
    };
    Ok(paths
        .into_iter()
        .map(|path| ExpressionPath {
            outcome: match path.outcome {
                ExpressionOutcome::Value(value) => ConditionTerm::nonzero_test(&value)
                    .map(|condition| {
                        native_comparison
                            .then(|| {
                                crate::kernel::machine_integer::comparison::native_narrow_comparison(
                                    &condition,
                                )
                            })
                            .flatten()
                            .unwrap_or(condition)
                    })
                    .map(ProgramValue::of_bool)
                    .map(ExpressionOutcome::Value)
                    .unwrap_or(ExpressionOutcome::RuntimeError(
                        RuntimeError::TypeMismatch,
                    )),
                outcome => outcome,
            },
            ..path
        })
        .collect())
}

/// A Rust operator on 8- or 16-bit values (`IntegerCastMode::NarrowArithmetic`):
/// the operands are evaluated as written, in order, and the value is the
/// operator's native node at `target_type`. An operand of another type is a
/// type mismatch, never a silent promotion.
fn evaluate_narrow_arithmetic_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    target_type: ProgramType,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    use crate::kernel::MachineBinaryOp as Op;
    let format = MachineIntegerType::from_program_type(target_type)
        .filter(|format| super::operators::is_narrow_format(*format));
    let outcome = |value: Option<ProgramValue>| match value {
        Some(value) => ExpressionOutcome::Value(value),
        None => ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
    };
    let (op, left, right) = match expression {
        ProgramExpression::Add(left, right) => (Op::Add, left, right),
        ProgramExpression::Subtract(left, right) => (Op::Subtract, left, right),
        ProgramExpression::Multiply(left, right) => (Op::Multiply, left, right),
        ProgramExpression::BitwiseAnd(left, right) => (Op::BitwiseAnd, left, right),
        ProgramExpression::BitwiseOr(left, right) => (Op::BitwiseOr, left, right),
        ProgramExpression::BitwiseXor(left, right) => (Op::BitwiseXor, left, right),
        ProgramExpression::ShiftLeft(left, right) => (Op::ShiftLeft, left, right),
        ProgramExpression::BitwiseNot(operand) => {
            return Ok(
                evaluate_program_expression_paths(state, operand, assumptions, budget)?
                    .into_iter()
                    .map(|path| ExpressionPath {
                        outcome: match path.outcome {
                            ExpressionOutcome::Value(value) => outcome(format.and_then(|format| {
                                super::operators::native_narrow_not(format, &value)
                            })),
                            outcome => outcome,
                        },
                        ..path
                    })
                    .collect(),
            );
        }
        _ => {
            return Ok(vec![ExpressionPath {
                outcome: outcome(None),
                facts: ExecutionFacts::new(),
                obligations: Vec::new(),
            }]);
        }
    };
    evaluate_program_value_binary_paths(
        state,
        left,
        right,
        assumptions,
        budget,
        |left, right, facts, obligations| {
            vec![ExpressionPath {
                outcome: outcome(format.and_then(|format| {
                    super::operators::native_narrow_binary(format, op, &left, &right)
                })),
                facts,
                obligations,
            }]
        },
    )
}

#[allow(clippy::too_many_arguments)] // Cast mode and pointee qualifiers are independent.
fn evaluate_program_cast_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    target_type: ProgramType,
    integer_mode: IntegerCastMode,
    pointee_struct_size: Option<u32>,
    pointee_volatile: bool,
    pointee_constant: bool,
    explicit_qualification: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    if integer_mode == IntegerCastMode::BoolValue {
        return evaluate_bool_value_paths(state, expression, assumptions, budget);
    }
    if integer_mode == IntegerCastMode::NarrowArithmetic {
        return evaluate_narrow_arithmetic_paths(
            state,
            expression,
            target_type,
            assumptions,
            budget,
        );
    }
    let _word_representation = target_type
        .is_pointer()
        .then(|| WordRepresentationScope::enter(true));
    let mut paths = Vec::new();
    for path in evaluate_program_expression_paths(state, expression, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            mut facts,
            mut obligations,
        } = path;
        // Converting a freed pointer to an integer (or to `_Bool`) uses its
        // indeterminate value; a pointer-to-pointer cast only retags it, like
        // a store. See `freed_pointer_use`.
        let outcome = match outcome {
            ExpressionOutcome::Value(value) if !target_type.is_pointer() => {
                match freed_pointer_use(state, &value, assumptions) {
                    Some(undefined_behavior) => {
                        ExpressionOutcome::UndefinedBehavior(undefined_behavior)
                    }
                    None => ExpressionOutcome::Value(value),
                }
            }
            outcome => outcome,
        };
        let outcome = match outcome {
            ExpressionOutcome::Value(value) => {
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                // A cast C source wrote, a C++20 integral conversion and a
                // Rust `as` convert modulo 2^N and owe nothing; any other
                // `Standard` cast owes the range. A modular conversion files
                // no identity with its operand: its node is the same
                // generic `Cast` a checked one builds, but nothing
                // establishes the range the identity needs.
                let conversion = if matches!(
                    integer_mode,
                    IntegerCastMode::CConversion
                        | IntegerCastMode::ResultConversion
                        | IntegerCastMode::Modulo
                ) {
                    IntegerConversion::Modular
                } else {
                    IntegerConversion::Checked
                };
                // A checked narrowing into an 8- or 16-bit type keeps its
                // operand, whose identity with the result it files below.
                let checked_source = (conversion == IntegerConversion::Checked
                    && matches!(
                        target_type,
                        ProgramType::Int8
                            | ProgramType::UInt8
                            | ProgramType::Int16
                            | ProgramType::UInt16
                    ))
                .then(|| value.clone());
                let needs_integer_origin = match &value {
                    ProgramValue::Int64(bits) | ProgramValue::UInt64(bits)
                        if target_type.is_pointer() =>
                    {
                        bits.uint64_as_const() != Some(0)
                            && effective_assumptions.decide(&ConditionTerm::uint64_equal(
                                bits.clone(),
                                MachineTerm::uint64_constant(0),
                            )) != Some(true)
                    }
                    _ => false,
                };
                let integer_pointer_origin = if needs_integer_origin {
                    Some(Address::symbolic(budget.allocate_kernel_variable()?))
                } else {
                    None
                };
                let word_bits = match &value {
                    ProgramValue::PointerInteger(record)
                        if target_type.is_pointer()
                            && matches!(record.kind, PointerIntegerKind::Word { .. })
                            && !SPECIFICATION_READS.with(|depth| depth.get() > 0) =>
                    {
                        crate::kernel::spec::program_value_bitvector_term(&record.numeric)
                    }
                    _ => None,
                };
                let first_conversion_obligation = obligations.len();
                let float_to_integer =
                    matches!(value, ProgramValue::Float32(_) | ProgramValue::Float64(_))
                        && MachineIntegerType::from_program_type(target_type).is_some()
                        && !SpecificationAccessScope::is_active();
                let pointer_operand = matches!(&value, ProgramValue::Pointer(_));
                let implicit_pointer_conversion = matches!(
                    integer_mode,
                    IntegerCastMode::CConversion | IntegerCastMode::ResultConversion
                ) && !explicit_qualification
                    && target_type.is_pointer()
                    && matches!(&value, ProgramValue::Pointer(_));
                let coerced = if integer_mode == IntegerCastMode::PointerCoercion
                    || implicit_pointer_conversion
                {
                    match value {
                        ProgramValue::Pointer(pointer)
                            if target_type.is_pointer()
                                && (integer_mode != IntegerCastMode::PointerCoercion
                                    || target_type != ProgramType::VoidPointer
                                    || pointer.program_type().is_object_pointer()) =>
                        {
                            // Of C's implicit pointer conversions, only one
                            // from `void *` reaches a character pointer, and
                            // it forms the byte view as a written one does.
                            // A coercion lowering inserts is a retype that
                            // keeps the value.
                            Ok(ProgramValue::Pointer(
                                if implicit_pointer_conversion
                                    && pointer.program_type() == ProgramType::VoidPointer
                                {
                                    cast_pointer_value(pointer, target_type)
                                } else {
                                    pointer.with_type(target_type)
                                },
                            ))
                        }
                        _ => Err(RuntimeError::TypeMismatch),
                    }
                } else if integer_mode == IntegerCastMode::Modulo {
                    MachineIntegerType::from_program_type(target_type)
                        .and_then(|destination| {
                            crate::kernel::machine_integer::conversion::convert_value(
                                value,
                                destination,
                            )
                        })
                        .ok_or(RuntimeError::TypeMismatch)
                } else if integer_mode == IntegerCastMode::UInt64BitsToInt64 {
                    match (target_type, value.numeric_value().clone()) {
                        (ProgramType::Int64, ProgramValue::UInt64(bits)) => Ok(
                            ProgramValue::Int64(MachineTerm::int64_from_uint64_bits(bits)),
                        ),
                        _ => Err(RuntimeError::TypeMismatch),
                    }
                } else if target_type == ProgramType::Int32 {
                    match value {
                        value @ (ProgramValue::Int8(_)
                        | ProgramValue::Int16(_)
                        | ProgramValue::UInt8(_)
                        | ProgramValue::UInt16(_)) => {
                            promote_program_path_value(value, MachineIntegerType::Int32)
                                .map(ProgramValue::Int32)
                                .ok_or(RuntimeError::TypeMismatch)
                        }
                        value => cast_program_value_to_type_with_integer_origin(
                            value,
                            target_type,
                            conversion,
                            &mut obligations,
                            &effective_assumptions,
                            integer_pointer_origin,
                        ),
                    }
                } else if target_type == ProgramType::UInt32
                    && matches!(
                        value,
                        ProgramValue::Int8(_)
                            | ProgramValue::Int16(_)
                            | ProgramValue::UInt8(_)
                            | ProgramValue::UInt16(_)
                    )
                {
                    // A narrow value's range was filed where the value was
                    // produced, in both orders for an unsigned type, so the
                    // widened word needs no fact of its own.
                    promote_program_path_value(value, MachineIntegerType::UInt32)
                        .map(ProgramValue::UInt32)
                        .ok_or(RuntimeError::TypeMismatch)
                } else {
                    cast_program_value_to_type_with_integer_origin(
                        value,
                        target_type,
                        conversion,
                        &mut obligations,
                        &effective_assumptions,
                        integer_pointer_origin,
                    )
                };
                if float_to_integer {
                    // Cast bounds belong to the statement's proof driver.
                    // Evaluation cannot assume them on its tentative path.
                    for obligation in &mut obligations[first_conversion_obligation..] {
                        obligation.assumable = false;
                    }
                }
                if let (Some(source), Ok(converted)) = (&checked_source, &coerced) {
                    facts.extend(
                        checked_narrowing_identity(source, converted)
                            .into_iter()
                            .map(ExecutionPureFact::certified),
                    );
                }
                let coerced = coerced.and_then(|value| {
                    let (Some(bits), ProgramValue::Pointer(pointer)) = (&word_bits, &value) else {
                        return Ok(value);
                    };
                    if effective_assumptions.decide(&ConditionTerm::uint64_equal(
                        bits.clone(),
                        MachineTerm::uint64_constant(0),
                    )) == Some(true)
                    {
                        return Ok(ProgramValue::typed_pointer(Address::null(), target_type));
                    }
                    // Conversion retains the pointer's structural domain. Checks
                    // resolve complete-value bounds without rewriting the value.
                    let pointer = pointer.clone();
                    let address = super::pointer_tags::cast_tagged_address_to_pointer(
                        bits,
                        &effective_assumptions,
                        &mut obligations,
                        target_type,
                    )
                    .map_err(RuntimeError::PointerConversion)?;
                    Ok(ProgramValue::Pointer(match address {
                        Some(address) => {
                            let class = pointer.object_class().or_else(|| address.object_class());
                            pointer
                                .with_address(address.address().clone())
                                .with_declared_object_class(class)
                        }
                        None => pointer,
                    }))
                });
                // A C conversion, a C++20 integral conversion or a Rust `as`
                // into a narrow type lands in that type's range whatever its
                // operand; file the range where the value is produced, as a
                // narrow read does.
                if let Ok(value) = &coerced
                    && matches!(
                        integer_mode,
                        IntegerCastMode::CConversion
                            | IntegerCastMode::ResultConversion
                            | IntegerCastMode::Modulo
                    )
                    && matches!(
                        crate::kernel::program_narrow_integer_range(value),
                        Some((
                            MachineTerm::Cast {
                                spelling: MachineCastSpelling::Generic,
                                ..
                            },
                            _,
                            _
                        ))
                    )
                {
                    add_narrow_integer_range_execution_pure_facts(&mut facts, assumptions, value);
                }
                let coerced = match (coerced, pointee_struct_size) {
                    (Ok(ProgramValue::Pointer(pointer)), Some(size)) if pointer_operand => Ok(
                        ProgramValue::Pointer(struct_view_of_initial_member(pointer, size)),
                    ),
                    (coerced, _) => coerced,
                };
                match coerced {
                    Ok(value) => {
                        // A cast the source wrote yields exactly the
                        // destination's qualification. Any other cast keeps
                        // a const source view. Neither affects whether the
                        // storage itself may be written.
                        let pointee_constant = pointee_constant
                            || (!explicit_qualification
                                && matches!(
                                    &value,
                                    ProgramValue::Pointer(pointer) if pointer.pointee_constant()
                                ));
                        let pointee_volatile = pointee_volatile
                            || (integer_mode == IntegerCastMode::PointerCoercion
                                && matches!(
                                    &value,
                                    ProgramValue::Pointer(pointer) if pointer.pointee_volatile()
                                ));
                        ExpressionOutcome::Value(
                            value
                                .with_pointer_pointee_volatile(pointee_volatile)
                                .with_pointer_pointee_constant(pointee_constant),
                        )
                    }
                    Err(error) => ExpressionOutcome::RuntimeError(error),
                }
            }
            ExpressionOutcome::UndefinedBehavior(error) => {
                ExpressionOutcome::UndefinedBehavior(error)
            }
            ExpressionOutcome::RuntimeError(error) => ExpressionOutcome::RuntimeError(error),
        };
        paths.push(ExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_program_float_classification_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    classification: FloatClassification,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_program_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            ExpressionOutcome::Value(ProgramValue::Float32(value)) => {
                paths.extend(condition_as_program_int32_paths(
                    ConditionTerm::float32_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            ExpressionOutcome::Value(ProgramValue::Float64(value)) => {
                paths.extend(condition_as_program_int32_paths(
                    ConditionTerm::float64_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            ExpressionOutcome::Value(_) => paths.push(ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                facts: path.facts,
                obligations: path.obligations,
            }),
            ExpressionOutcome::UndefinedBehavior(error) => paths.push(ExpressionPath {
                outcome: ExpressionOutcome::UndefinedBehavior(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
            ExpressionOutcome::RuntimeError(error) => paths.push(ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_program_float_negate_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_program_expression_paths(state, expression, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = path;
        let outcome = match outcome {
            ExpressionOutcome::Value(ProgramValue::Float32(value)) => {
                ExpressionOutcome::Value(ProgramValue::Float32(MachineTerm::float32_negate(value)))
            }
            ExpressionOutcome::Value(ProgramValue::Float64(value)) => {
                ExpressionOutcome::Value(ProgramValue::Float64(MachineTerm::float64_negate(value)))
            }
            ExpressionOutcome::Value(_) => {
                ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
            }
            ExpressionOutcome::UndefinedBehavior(error) => {
                ExpressionOutcome::UndefinedBehavior(error)
            }
            ExpressionOutcome::RuntimeError(error) => ExpressionOutcome::RuntimeError(error),
        };
        paths.push(ExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// An enum value of `variant` built from `fields`, evaluated in order. Each
/// field must have its declared type: the frontend's types are checked, not
/// trusted.
pub(super) fn evaluate_program_enum_construct_paths(
    state: &ExecutionState,
    enum_type: TypeParameterName,
    variant: &str,
    fields: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath<crate::kernel::execution_value::ExecutionValue>>> {
    let algebraic_type = enum_type.algebraic_type();
    let declared = algebraic_type
        .variants
        .iter()
        .find(|declared| declared.name == variant)
        .map(|declared| declared.fields.clone());
    let mut paths = Vec::new();
    for path in crate::kernel::functions::evaluate_retained_program_arguments_paths(
        state,
        fields,
        assumptions,
        budget,
        None,
    )? {
        let outcome = match path.outcome {
            Some(FunctionOutcome::UndefinedBehavior(error)) => {
                ExpressionOutcome::UndefinedBehavior(error)
            }
            Some(FunctionOutcome::RuntimeError(error)) => ExpressionOutcome::RuntimeError(error),
            Some(_) => ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
            None => match &declared {
                Some(declared)
                    if !algebraic_type.rigid
                        && declared.len() == path.values.len()
                        && let Some(fields) = declared
                            .iter()
                            .zip(path.values)
                            .map(|(declared, value)| retained_enum_field_value(declared, value))
                            .collect::<Option<Vec<_>>>() =>
                {
                    ExpressionOutcome::Value(
                        crate::kernel::KernelConstructor {
                            algebraic_type: algebraic_type.clone(),
                            variant: variant.to_string(),
                            fields,
                        }
                        .into_term()
                        .into(),
                    )
                }
                _ => ExpressionOutcome::RuntimeError(RuntimeError::EnumVariant(format!(
                    "`{}::{variant}` is not a variant of these field types",
                    algebraic_type.name
                ))),
            },
        };
        paths.push(ExpressionPath {
            outcome,
            facts: path.facts,
            obligations: path.obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Preserve the selected field's root, while retaining the native distinction
/// between logical algebraic fields and program-carried type parameters.
fn retained_enum_field_value(
    declared: &AlgebraicValueType,
    value: crate::kernel::execution_value::ExecutionValue,
) -> Option<KernelTerm> {
    // A logical field holds the value's mathematical observation, never a C
    // representation record: a 64-bit C integer that may carry pointer
    // provenance is stored as the plain `int64` a Click expression writes,
    // so the constructor a C call builds is the one a proof writes.
    if matches!(declared, AlgebraicValueType::Program(_))
        && let ProgramValue::PointerInteger(_) = value.native().as_ref()
    {
        let numeric = value.native().numeric_value().clone();
        return enum_field_value(declared, numeric)
            .map(|field| KernelTermImport::default().match_field(&field));
    }
    if let Some(root) = value.shared() {
        if matches!(declared, AlgebraicValueType::Algebraic { .. })
            && let KernelType::Algebraic(ty) = root.ty()
            && ty.value_type() == *declared
        {
            return Some(root.clone());
        }
        if matches!(declared, AlgebraicValueType::Program(ty)
            if *ty == value.program_type() && !matches!(ty, ProgramType::Parameter(_)))
        {
            return Some(root.clone());
        }
    }
    enum_field_value(declared, value.into_native())
        .map(|field| KernelTermImport::default().match_field(&field))
}

/// The field a constructor stores for C value `value` of a field declared
/// `declared`: the value itself, or, for a field of a nested enum type such
/// as `Result<u32, ParseError>`'s error, the enum value a C local of that
/// enum holds.
fn enum_field_value(declared: &AlgebraicValueType, value: ProgramValue) -> Option<AlgebraicValue> {
    match (declared, value) {
        (AlgebraicValueType::Algebraic { .. }, ProgramValue::Parameter(term))
            if term.algebraic_type.value_type() == *declared =>
        {
            Some(AlgebraicValue::Algebraic(*term))
        }
        (declared, value) => declared
            .accepts_program_value(&value)
            .then_some(AlgebraicValue::Program(value)),
    }
}

/// Field `index` of an enum value. The value must be a constructor of
/// `variant`: a `match` arm makes the value it matches one, so a field a
/// Rust arm reads is always that arm's. Anything else is refused rather than
/// given an unconstrained value.
pub(super) fn evaluate_program_enum_field_paths(
    state: &ExecutionState,
    value: &ProgramExpression,
    variant: &str,
    index: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath<crate::kernel::execution_value::ExecutionValue>>> {
    let mut paths = Vec::new();
    for path in super::retained_expression::evaluate_expression_value_paths(
        state,
        value,
        assumptions,
        budget,
    )? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = path;
        if let ExpressionOutcome::Value(value) = &outcome
            && let Some(root) = value.shared()
            && let KernelTermNode::Constructor(constructor) = root.node()
        {
            let outcome = if constructor.variant != variant {
                ExpressionOutcome::RuntimeError(RuntimeError::EnumVariant(format!(
                    "a field of `{}::{variant}` is read from a value not known to be that variant",
                    constructor.algebraic_type.name
                )))
            } else if let Some(field) = constructor.field(variant, index) {
                if field.ty() == &KernelType::Integer {
                    ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
                } else if let KernelTermNode::Legacy(value) = field.node() {
                    let PureFunctionArgument::Value(value) = value.value() else {
                        unreachable!("program enum field");
                    };
                    ExpressionOutcome::Value(
                        crate::kernel::execution_value::ExecutionValue::retain_native(
                            value.clone(),
                        ),
                    )
                } else {
                    ExpressionOutcome::Value(field.clone().into())
                }
            } else {
                ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
            };
            paths.push(ExpressionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        }
        // Unknown variants retain the existing fact-witness authority boundary.
        let outcome = match outcome
            .map_value(crate::kernel::execution_value::ExecutionValue::into_native)
        {
            ExpressionOutcome::Value(ProgramValue::Parameter(term)) => {
                match &known_enum_constructor(&term, &facts, assumptions)
                    .unwrap_or_else(|| term.as_ref().clone())
                    .node
                {
                    AlgebraicTermNode::Constructor {
                        variant: actual,
                        fields,
                    } if actual == variant => match fields.get(index) {
                        Some(AlgebraicValue::Program(field)) => {
                            ExpressionOutcome::Value(field.clone())
                        }
                        // A nested enum field is the value a C local of that
                        // enum holds.
                        Some(AlgebraicValue::Algebraic(field)) => ExpressionOutcome::Value(
                            ProgramValue::Parameter(Box::new(field.clone())),
                        ),
                        _ => ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    },
                    _ => ExpressionOutcome::RuntimeError(RuntimeError::EnumVariant(format!(
                        "a field of `{}::{variant}` is read from a value not known to be that variant",
                        term.algebraic_type.name
                    ))),
                }
            }
            ExpressionOutcome::Value(_) => {
                ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
            }
            outcome => outcome,
        };
        paths.push(ExpressionPath {
            outcome: outcome
                .map_value(crate::kernel::execution_value::ExecutionValue::retain_native),
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// The constructor `term` is known to be: itself, or one the facts equate
/// it to. Reads the path's own facts and the context's index; never
/// rebuilds a context.
pub(in crate::kernel) fn known_enum_constructor(
    term: &AlgebraicTerm,
    facts: &ExecutionFacts,
    assumptions: &PureFactContext,
) -> Option<AlgebraicTerm> {
    if matches!(term.node, AlgebraicTermNode::Constructor { .. }) {
        return Some(term.clone());
    }
    facts
        .fact_iter()
        .find_map(|fact| match fact.proposition() {
            Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))
                if left.native_compat() == term
                    && matches!(
                        right.native_compat().node,
                        AlgebraicTermNode::Constructor { .. }
                    ) =>
            {
                Some(right.native_compat().clone())
            }
            _ => None,
        })
        .or_else(|| assumptions.known_algebraic_constructor(term))
}

/// One path per variant `term` can still be, each with the constructor it
/// is: the known one alone, or a constructor of fresh fields, ranged over
/// their types, with the equation a proof `match` arm states as a path
/// fact. Variants the facts refute get no path.
pub(in crate::kernel) fn enum_variant_paths(
    term: &AlgebraicTerm,
    facts: &ExecutionFacts,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<(AlgebraicTerm, ExecutionFacts)>, RuntimeError>> {
    if let Some(known) = known_enum_constructor(term, facts, assumptions) {
        return Ok(Ok(vec![(known, facts.clone())]));
    }
    let mut paths = Vec::new();
    for variant in term.algebraic_type.variants.iter() {
        let mut fields = Vec::with_capacity(variant.fields.len());
        for field in &variant.fields {
            let variable = budget.allocate_kernel_variable()?;
            // A nested enum field is a fresh value of that enum.
            if let AlgebraicValueType::Algebraic { .. } = field
                && let Some(nested) = term.algebraic_type.resolve_nested_type(field)
            {
                fields.push(AlgebraicValue::Algebraic(AlgebraicTerm {
                    algebraic_type: nested,
                    node: AlgebraicTermNode::Variable(variable),
                }));
                continue;
            }
            let Some(value) = field.symbolic_program_value(variable) else {
                return Ok(Err(RuntimeError::EnumVariant(format!(
                    "`{}::{}` has a field that is not a C value",
                    term.algebraic_type.name, variant.name
                ))));
            };
            fields.push(AlgebraicValue::Program(value));
        }
        let mut case_facts = facts.clone();
        // A fresh narrow field ranges over its type's values only.
        for field in &fields {
            if let AlgebraicValue::Program(value) = field {
                add_narrow_integer_range_execution_pure_facts(&mut case_facts, assumptions, value);
            }
        }
        let constructor = AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: variant.name.clone(),
                fields,
            },
        };
        let condition =
            ConditionTerm::AlgebraicEqual(Box::new(term.clone()), Box::new(constructor.clone()));
        match decide_with_facts(assumptions, &case_facts, &condition) {
            Some(false) => continue,
            Some(true) => {}
            None => {
                if add_path_fact(
                    &mut case_facts,
                    assumptions,
                    Proposition::Equal(
                        Term::Algebraic(term.clone().into()),
                        Term::Algebraic(constructor.clone().into()),
                    ),
                )
                .is_none()
                {
                    continue;
                }
            }
        }
        paths.push((constructor, case_facts));
    }
    Ok(Ok(paths))
}

/// `value is variant` as a `bool`, on each path [`enum_variant_paths`]
/// splits `value` into.
/// `term is variant` as one `Bool`, without splitting `term` into its
/// variants: beside a live state a split cannot invent the fields' witnesses
/// ([`ExecutionBudget::beside_live_state`]). A variant without fields is the
/// equation with its constructor; when every other variant is without
/// fields, as `Option::Some` is, it is unequal to each of theirs. `None` for
/// a type with two variants that carry fields.
fn enum_is_without_witnesses(term: &AlgebraicTerm, variant: &str) -> Option<ConditionTerm> {
    let equals = |name: &str| {
        ConditionTerm::AlgebraicEqual(
            Box::new(term.clone()),
            Box::new(AlgebraicTerm {
                algebraic_type: term.algebraic_type.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: name.to_string(),
                    fields: Vec::new(),
                },
            }),
        )
    };
    let variants = &term.algebraic_type.variants;
    let tested = variants.iter().find(|schema| schema.name == variant)?;
    if tested.fields.is_empty() {
        return Some(equals(variant));
    }
    let others = variants.iter().filter(|schema| schema.name != variant);
    if others.clone().any(|schema| !schema.fields.is_empty()) {
        return None;
    }
    Some(others.fold(ConditionTerm::Constant(true), |all, schema| {
        ConditionTerm::bool_if(
            all,
            ConditionTerm::bool_not(equals(&schema.name)),
            ConditionTerm::Constant(false),
        )
    }))
}

fn evaluate_program_enum_is_paths(
    state: &ExecutionState,
    value: &ProgramExpression,
    variant: &str,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_program_expression_paths(state, value, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = path;
        let term = match outcome {
            ExpressionOutcome::Value(ProgramValue::Parameter(term))
                if !term.algebraic_type.rigid =>
            {
                term
            }
            ExpressionOutcome::Value(_) => {
                paths.push(ExpressionPath {
                    outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    facts,
                    obligations,
                });
                continue;
            }
            outcome => {
                paths.push(ExpressionPath {
                    outcome,
                    facts,
                    obligations,
                });
                continue;
            }
        };
        if budget.refuses_execution_identities()
            && known_enum_constructor(&term, &facts, assumptions).is_none()
            && let Some(test) = enum_is_without_witnesses(&term, variant)
        {
            paths.push(ExpressionPath {
                outcome: ExpressionOutcome::Value(ProgramValue::of_bool(test)),
                facts,
                obligations,
            });
            continue;
        }
        match enum_variant_paths(&term, &facts, assumptions, budget)? {
            Ok(cases) => {
                for (constructor, case_facts) in cases {
                    let AlgebraicTermNode::Constructor {
                        variant: actual, ..
                    } = &constructor.node
                    else {
                        unreachable!("variant paths carry constructors");
                    };
                    paths.push(ExpressionPath {
                        outcome: ExpressionOutcome::Value(ProgramValue::bool_constant(
                            actual == variant,
                        )),
                        facts: case_facts,
                        obligations: obligations.clone(),
                    });
                }
            }
            Err(error) => paths.push(ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(error),
                facts,
                obligations,
            }),
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_program_conditional_paths(
    state: &ExecutionState,
    condition: &ProgramExpression,
    then_branch: &ProgramExpression,
    else_branch: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_program_condition_paths(state, condition, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let ExpressionOutcome::Value(value) = outcome else {
            paths.push(ExpressionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };

        for truthiness in program_truthiness_paths(value, facts, obligations, assumptions) {
            let branch = if truthiness.is_true {
                then_branch
            } else {
                else_branch
            };
            let branch_assumptions = assumptions_with_path_context(
                assumptions,
                &truthiness.facts,
                &truthiness.obligations,
            );
            for branch_path in
                evaluate_program_expression_paths(state, branch, &branch_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &truthiness.facts,
                    &truthiness.obligations,
                    &branch_path.facts,
                    &branch_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                paths.push(ExpressionPath {
                    outcome: branch_path.outcome,
                    facts,
                    obligations,
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_program_lvalue_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<LValuePath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        ProgramExpression::Variable(name) => vec![LValuePath {
            outcome: match state.locals.binding(name) {
                Some(LocalBinding::Object {
                    program_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                })
                | Some(LocalBinding::UninitializedObject {
                    program_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                }) => {
                    let lvalue = LValue::local_with_qualifiers(
                        name.clone(),
                        *program_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant);
                    LValueOutcome::LValue(lvalue)
                }
                Some(LocalBinding::GlobalObject {
                    program_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                }) => LValueOutcome::LValue(
                    LValue::memory_with_qualifiers(
                        slot.clone(),
                        *program_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant),
                ),
                Some(LocalBinding::ArrayObject { .. }) => {
                    LValueOutcome::RuntimeError(RuntimeError::TypeMismatch)
                }
                // A struct object is an lvalue whose address is the object's
                // slot; its value type is the byte array holding it.
                Some(LocalBinding::AggregateObject { layout, .. }) => LValueOutcome::LValue(
                    LValue::local(name.clone(), ProgramType::UInt8Array(layout.size_bytes())),
                ),
                None => match name.static_id().and_then(|id| id.metadata()) {
                    Some(metadata) if metadata.array_shape.is_none() => LValueOutcome::LValue(
                        LValue::memory_with_qualifiers(
                            SymbolicMemory::global_pointer(name),
                            metadata.program_type,
                            metadata.volatile,
                            metadata.pointee_volatile,
                        )
                        .with_constant(metadata.constant)
                        .with_pointee_constant(metadata.pointee_constant),
                    ),
                    Some(_) => LValueOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    None => {
                        LValueOutcome::RuntimeError(RuntimeError::UnboundVariable(name.to_string()))
                    }
                },
            },
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        ProgramExpression::Load(pointer_expression) => {
            let Some(value_type) = program_expression_pointee_type(state, pointer_expression)
            else {
                return Ok(vec![LValuePath {
                    outcome: LValueOutcome::RuntimeError(RuntimeError::IndeterminatePointeeType),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_program_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => LValuePath {
                        outcome: LValueOutcome::LValue(
                            LValue::memory_with_volatile(
                                pointer.address().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_bounds_of(&pointer)
                            .with_access_class(CAccessClass::of_kernel_type(value_type)),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::Value(_) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => LValuePath {
                        outcome: LValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::RuntimeError(error) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        ProgramExpression::TypedLoad {
            pointer: pointer_expression,
            value_type,
            volatile,
            pointee_constant,
            access_class,
            ..
        } => {
            let access_class = access_class
                .clone()
                .or_else(|| CAccessClass::of_kernel_type(*value_type));
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_program_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => LValuePath {
                        outcome: LValueOutcome::LValue(
                            LValue::memory_with_volatile(
                                pointer.address().clone(),
                                *value_type,
                                *volatile || pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_pointee_constant(*pointee_constant)
                            .with_bounds_of(&pointer)
                            .with_access_class(access_class.clone()),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::Value(_) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => LValuePath {
                        outcome: LValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::RuntimeError(error) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        ProgramExpression::Index(base, index) => {
            let Some(value_type) = program_expression_pointee_type(state, base) else {
                return Ok(vec![LValuePath {
                    outcome: LValueOutcome::RuntimeError(RuntimeError::IndeterminatePointeeType),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in evaluate_program_add_paths(state, base, index, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => LValuePath {
                        outcome: LValueOutcome::LValue(
                            LValue::memory_with_volatile(
                                pointer.address().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_bounds_of(&pointer)
                            .with_access_class(CAccessClass::of_kernel_type(value_type)),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::Value(_) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => LValuePath {
                        outcome: LValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    ExpressionOutcome::RuntimeError(error) => LValuePath {
                        outcome: LValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        _ => vec![LValuePath {
            outcome: LValueOutcome::RuntimeError(RuntimeError::TypeMismatch),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn read_program_lvalue_expression_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    Ok(
        read_retained_lvalue_expression_paths(state, expression, assumptions, budget)?
            .into_iter()
            .map(ExecutionValuePath::into_native)
            .collect(),
    )
}

pub(in crate::kernel) fn read_program_lvalue_paths(
    state: &ExecutionState,
    outcome: LValueOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    source: Option<&LoadSourceId>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    Ok(read_retained_lvalue_paths(
        state,
        outcome,
        facts,
        obligations,
        source,
        assumptions,
        budget,
    )?
    .into_iter()
    .map(ExecutionValuePath::into_native)
    .collect())
}

fn retained_value_accepted(ty: ProgramType, value: &ExecutionValue) -> bool {
    if value.shared().is_some()
        && matches!(
            value.program_type(),
            ProgramType::Float32
                | ProgramType::Float64
                | ProgramType::Int8
                | ProgramType::Int16
                | ProgramType::Int32
                | ProgramType::Int64
                | ProgramType::UInt8
                | ProgramType::UInt16
                | ProgramType::UInt32
                | ProgramType::UInt64
        )
    {
        return value.program_type() == ty;
    }
    ty.accepts(&value.native())
}

pub(in crate::kernel) fn read_retained_lvalue_expression_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    let source = match expression {
        ProgramExpression::TypedLoad { source, .. } => source.as_ref(),
        _ => None,
    };
    let mut paths = Vec::new();
    for lvalue_path in evaluate_program_lvalue_paths(state, expression, assumptions, budget)? {
        paths.extend(read_retained_lvalue_paths(
            state,
            lvalue_path.outcome,
            lvalue_path.facts,
            lvalue_path.obligations,
            source,
            assumptions,
            budget,
        )?);
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Reads an lvalue, filing the type range of each narrow integer value the
/// read produces.
///
/// A narrow value is in its type's range wherever one exists (see
/// [`crate::kernel::c_narrow_integer_range_facts`]), and a parameter's range
/// is an entry fact. Every other narrow value an expression can hold -- a
/// loaded cell, a local a loop or a call gave a fresh value -- enters it
/// through this read or as a substituted `ProgramExpression::Value`, so the range
/// is filed at those two points, once where the value is produced, and no
/// operator that later widens the value restates it. A range the context
/// already holds exactly is not refiled.
pub(in crate::kernel) fn read_retained_lvalue_paths(
    state: &ExecutionState,
    outcome: LValueOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    source: Option<&LoadSourceId>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    let mut paths = read_retained_lvalue_paths_without_ranges(
        state,
        outcome,
        facts,
        obligations,
        source,
        assumptions,
        budget,
    )?;
    for path in &mut paths {
        let ExpressionOutcome::Value(value) = &path.outcome else {
            continue;
        };
        add_retained_local_range_facts(&mut path.facts, assumptions, value);
    }
    Ok(paths)
}

fn add_retained_local_range_facts(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    value: &ExecutionValue,
) {
    if let Some(native) = value.native_payload() {
        return add_narrow_integer_range_execution_pure_facts(facts, assumptions, native);
    }
    if let Some(root) = value.shared()
        && matches!(root.node(), KernelTermNode::BoolCast { .. })
        && let Some(format) = MachineIntegerType::from_program_type(value.program_type())
    {
        let native = format.value_from_term(
            root.machine_conversion_leaf()
                .expect("Boolean cast")
                .clone(),
        );
        add_narrow_integer_range_execution_pure_facts(facts, assumptions, &native);
    }
}

/// A successful C access supplies the value. The call output receipt
/// gives the same read a proof name, including reads through a local binding.
fn record_call_output_read(
    state: &ExecutionState,
    lvalue: &LValue,
    pointer: &Address,
    outcome: &ExpressionOutcome<ExecutionValue>,
    facts: &mut ExecutionFacts,
) {
    if lvalue.is_volatile()
        || SpecificationAccessScope::is_active()
        || !ProgramPoint::supports_local_call_output(pointer)
    {
        return;
    }
    let ExpressionOutcome::Value(value) = outcome else {
        return;
    };
    let Some(format) = MachineIntegerType::from_program_type(lvalue.value_type) else {
        return;
    };
    let kind = LoadKind::of_type(lvalue.value_type).expect("integer call output");
    let Some(version) = state
        .program_point()
        .call_output_integer_version(pointer, kind)
    else {
        return;
    };
    let value = value.native();
    let value = value.numeric_value();
    if !LoadKind::of_value(value).is_some_and(|value_kind| kind.reads_word_of(value_kind)) {
        return;
    }
    let Some(bits) = crate::kernel::spec::program_value_bitvector_term(value) else {
        return;
    };
    let read = scalar_read_for_exact_cell_at(&version, pointer, kind, kind.byte_width());
    if bits == read {
        return;
    }
    let comparison = if matches!(
        format,
        MachineIntegerType::Int128 | MachineIntegerType::UInt128
    ) {
        let Some(comparison) = wide_integer_comparison_condition(
            ComparisonOperator::Equal,
            &format.value_from_term(read),
            value,
        ) else {
            return;
        };
        comparison
    } else {
        ConditionTerm::machine_compare(format, CompareRelation::Equal, read, bits)
    };
    facts.push(ExecutionPureFact {
        logical_read_equation: true,
        ..ExecutionPureFact::certified(Proposition::condition_is(comparison, true))
    });
}

fn read_retained_lvalue_paths_without_ranges(
    state: &ExecutionState,
    outcome: LValueOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    source: Option<&LoadSourceId>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    // A scalar declared without a value whose storage a callee's checked
    // postcondition states `defined` is read from that storage: the call
    // wrote it through its address, which the name's binding never sees.
    if let LValueOutcome::LValue(lvalue) = &outcome
        && let LValueStorage::Local { name } = &lvalue.storage
        && let Some(LocalBinding::UninitializedObject {
            program_type,
            slot,
            volatile,
            pointee_volatile,
            ..
        }) = state.locals.binding(name)
        && assumptions.has_memory_read_defined_evidence(&state.memory, slot, *program_type)
    {
        let memory = LValue::memory_with_qualifiers(
            slot.clone(),
            *program_type,
            *volatile,
            *pointee_volatile,
        );
        return read_retained_lvalue_paths_without_ranges(
            state,
            LValueOutcome::LValue(memory),
            facts,
            obligations,
            source,
            assumptions,
            budget,
        );
    }
    Ok(match outcome {
        LValueOutcome::LValue(lvalue) => match &lvalue.storage {
            LValueStorage::Local { name } => {
                let local_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                if let Some(pointer) = state.locals.slot(name)
                    && let Some(refusal) = subobject_access_refusal(
                        pointer,
                        &lvalue,
                        crate::kernel::AccessExtent::of_type(lvalue.value_type),
                        &facts,
                        &obligations,
                        &local_assumptions,
                    )
                {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    }]);
                }
                if let Some(pointer) = state.locals.slot(name)
                    && lvalue.provenance.as_deref().is_some_and(|origin| {
                        !local_assumptions.provenance_equal(origin, &pointer.object_identity())
                            || !lvalue.bounds_known && lvalue.bounds_owner.is_some()
                    })
                    && !state.resources().permits_designated_memory_read(
                        pointer,
                        lvalue.access_provenance(),
                        lvalue.value_type.byte_width(),
                        &local_assumptions,
                    )
                {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::MissingResource {
                            resource: Box::new(ResourceFact::view_memory(
                                MemoryRange::new_with_element_width(
                                    pointer.clone(),
                                    0u32.into(),
                                    1u32.into(),
                                    lvalue.value_type.byte_width(),
                                ),
                            )),
                        }),
                        facts,
                        obligations,
                    }]);
                }
                if matches!(
                    state.locals.binding(name),
                    Some(
                        LocalBinding::Object {
                            storage_declared: true,
                            ..
                        } | LocalBinding::UninitializedObject { .. }
                    )
                ) && let Some(pointer) = state.locals.slot(name)
                    && state.memory.requires_explicit_scalar_ownership(pointer)
                    && !assumptions.should_allow_symbolic_contract_loads()
                    && !local_read_permitted(state, pointer, lvalue.value_type, assumptions)
                {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::MissingResource {
                            resource: Box::new(ResourceFact::view_memory(MemoryRange::access(
                                pointer.clone(),
                                lvalue.value_type,
                            ))),
                        }),
                        facts,
                        obligations,
                    }]);
                }
                let outcome = match state.locals.get(name) {
                    Some(value) if retained_value_accepted(lvalue.value_type, value) => {
                        let value =
                            if value.shared().is_some() && !value.program_type().is_pointer() {
                                value.clone().into_value()
                            } else {
                                let native = value.native();
                                let native = native
                                    .into_owned()
                                    .with_pointer_pointee_volatile(lvalue.pointee_is_volatile())
                                    .with_pointer_pointee_constant(lvalue.pointee_is_constant());
                                if native.program_type().is_pointer() {
                                    value.retain_checked_pointer(native)
                                } else {
                                    native.into()
                                }
                            };
                        ExpressionOutcome::Value(value)
                    }
                    Some(_) => ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    None if matches!(
                        state.locals.binding(name),
                        Some(LocalBinding::UninitializedObject { .. })
                    ) =>
                    {
                        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead)
                    }
                    None => ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(
                        name.to_string(),
                    )),
                };
                let mut facts = facts;
                if let Some(pointer) = state.locals.slot(name) {
                    record_call_output_read(state, &lvalue, pointer, &outcome, &mut facts);
                }
                if lvalue.is_volatile()
                    && !SpecificationAccessScope::is_active()
                    && let ExpressionOutcome::Value(value) = &outcome
                    && let Some(pointer) = lvalue.pointer(state)
                {
                    facts.push(volatile_access_fact(
                        budget,
                        VolatileAccessKind::Read,
                        pointer,
                        lvalue.value_type,
                        value.clone(),
                    )?);
                }
                vec![ExecutionValuePath {
                    outcome,
                    facts,
                    obligations,
                }]
            }
            LValueStorage::Memory { pointer } => {
                if state
                    .memory
                    .heap
                    .pending_reallocations
                    .values()
                    .any(|pending| pending.old_pointer.base == pointer.base)
                {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::RuntimeError(
                            RuntimeError::UnresolvedAllocationOutcome,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                if state.memory.is_ended_local_address(pointer) {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::UndefinedBehavior(
                            UndefinedBehavior::InvalidMemory,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                if state
                    .memory
                    .is_deallocated_heap_address(pointer, assumptions)
                {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::UndefinedBehavior(
                            UndefinedBehavior::InvalidMemory,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                if let Some(refusal) = subobject_access_refusal(
                    pointer,
                    &lvalue,
                    crate::kernel::AccessExtent::of_type(lvalue.value_type),
                    &facts,
                    &obligations,
                    &effective_assumptions,
                )
                .or_else(|| {
                    (!SpecificationAccessScope::is_active())
                        .then(|| effective_type_refusal(&state.memory, pointer, &lvalue))
                        .flatten()
                }) {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    }]);
                }
                let is_external = is_external_memory_pointer(pointer)
                    || state.memory.requires_explicit_scalar_ownership(pointer)
                    || lvalue.provenance.as_deref().is_some_and(|origin| {
                        !effective_assumptions.provenance_equal(origin, &pointer.object_identity())
                            || !lvalue.bounds_known && lvalue.bounds_owner.is_some()
                    });
                let require_owned = assumptions.should_require_owned_expression_loads();
                // An aggregate a call returns by value is a fresh object the
                // abstract machine creates for its caller alone, which no
                // resource can name; a contract reads its fields, as
                // `nodes(result.head)` does, before the caller copies it out.
                let returned_aggregate = SpecificationAccessScope::is_active()
                    && matches!(pointer.base, AddressBase::Temporary(_));
                // A value of an abstract type is read whole: its object.
                let abstract_object = matches!(lvalue.value_type,
                    ProgramType::Parameter(parameter) if parameter.has_abstract_size());
                let has_read_resource = (is_external || require_owned)
                    && (returned_aggregate
                        || (!require_owned && assumptions.should_allow_symbolic_contract_loads())
                        || crate::kernel::api::with_extended_dag_bridging(|| {
                            if abstract_object {
                                state.resources().permits_object_access(
                                    &MemoryRange::access(pointer.clone(), lvalue.value_type),
                                    false,
                                    &effective_assumptions,
                                )
                            } else {
                                state.resources().permits_designated_memory_read(
                                    pointer,
                                    lvalue.access_provenance(),
                                    lvalue.value_type.byte_width(),
                                    &effective_assumptions,
                                )
                            }
                        }));
                if (is_external || require_owned) && !has_read_resource && abstract_object {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::MissingResource {
                            resource: Box::new(ResourceFact::view_memory(MemoryRange::access(
                                pointer.clone(),
                                lvalue.value_type,
                            ))),
                        }),
                        facts,
                        obligations,
                    }]);
                }
                if (is_external || require_owned) && !has_read_resource {
                    return Ok(vec![ExecutionValuePath {
                        outcome: ExpressionOutcome::RuntimeError(RuntimeError::MissingResource {
                            resource: Box::new(ResourceFact::view_memory(
                                MemoryRange::new_with_element_width(
                                    pointer.clone(),
                                    MachineTerm::constant(0),
                                    MachineTerm::constant(1),
                                    // The element the permission check
                                    // counts: a loaded pointer is one
                                    // four-byte logical field.
                                    crate::kernel::assumptions::read_candidate_byte_width(
                                        lvalue.value_type.byte_width(),
                                    ),
                                ),
                            )),
                        }),
                        facts,
                        obligations,
                    }]);
                }
                let bit_field_mask = match lvalue.access_class() {
                    Some(CAccessClass::BitFieldByte(mask)) => Some(mask.get()),
                    _ => None,
                };
                if let Some(mask) = bit_field_mask {
                    let resolved =
                        resolve_local_pointer_alias(state, pointer, &effective_assumptions);
                    if !resolved.base.is_local_block()
                        || !state.memory.access_in_bounds(&resolved, 1)
                    {
                        return Ok(vec![ExecutionValuePath {
                            outcome: ExpressionOutcome::UndefinedBehavior(
                                UndefinedBehavior::InvalidMemory,
                            ),
                            facts,
                            obligations,
                        }]);
                    }
                    if let Some(byte) = state.memory.heap.initialized.partial_byte(&resolved) {
                        let outcome = if byte.mask & mask != mask {
                            ExpressionOutcome::UndefinedBehavior(
                                UndefinedBehavior::UninitializedRead,
                            )
                        } else if let Some(ProgramValue::UInt8(value)) = &byte.value {
                            ExpressionOutcome::Value(
                                ProgramValue::UInt8(super::byte_view::mask_byte(
                                    value.clone(),
                                    mask,
                                ))
                                .into(),
                            )
                        } else {
                            ExpressionOutcome::RuntimeError(RuntimeError::FunctionContract(
                                "bit-field read requires a retained value for the selected bits"
                                    .into(),
                            ))
                        };
                        return Ok(vec![ExecutionValuePath {
                            outcome,
                            facts,
                            obligations,
                        }]);
                    }
                }
                let can_name_read = !lvalue.is_volatile() || SpecificationAccessScope::is_active();
                let uses_entry_version = has_read_resource
                    && (lvalue.value_type.is_pointer()
                        || matches!(
                            lvalue.value_type,
                            ProgramType::Int8
                                | ProgramType::UInt8
                                | ProgramType::Int16
                                | ProgramType::UInt16
                                | ProgramType::Int32
                                | ProgramType::UInt32
                                | ProgramType::Int64
                                | ProgramType::UInt64
                                | ProgramType::Int128
                                | ProgramType::UInt128
                                | ProgramType::Parameter(_)
                        ))
                    && pointer.base == AddressBase::ExternalArgument
                    && can_name_read;
                let origin = (uses_entry_version
                    || (can_name_read
                        && (lvalue.value_type == ProgramType::Bool
                            || crate::kernel::KernelFloatType::from_program_type(
                                lvalue.value_type,
                            )
                            .is_some())))
                .then(|| state.program_point());
                let entry_read = origin.as_ref().and_then(|point| {
                    let entry = match lvalue.value_type {
                        ProgramType::Int8
                        | ProgramType::UInt8
                        | ProgramType::Int16
                        | ProgramType::UInt16
                        | ProgramType::Int32
                        | ProgramType::Int64
                        | ProgramType::UInt64
                        | ProgramType::Int128
                        | ProgramType::UInt128 => point
                            .entry_integer_version(pointer, LoadKind::of_type(lvalue.value_type)?),
                        ProgramType::Parameter(parameter) => {
                            point.generic_entry_version(pointer, parameter)
                        }
                        _ => None,
                    }?;
                    Some((entry, point))
                });
                let mut paths = if let Some((entry, point)) = entry_read {
                    vec![
                        super::memory_loads::evaluate_indexed_read(
                            entry,
                            point,
                            pointer.clone(),
                            lvalue.value_type,
                            facts,
                            obligations,
                        )
                        .map_value(Into::into),
                    ]
                } else {
                    evaluate_retained_memory_load_paths(
                        &state.memory,
                        pointer.clone(),
                        lvalue.value_type,
                        facts,
                        obligations,
                        assumptions,
                        is_external && has_read_resource,
                        lvalue.is_volatile() && !SpecificationAccessScope::is_active(),
                        source,
                        budget.program_byte_order(),
                        origin.as_ref(),
                    )
                };
                for path in &mut paths {
                    record_call_output_read(
                        state,
                        &lvalue,
                        pointer,
                        &path.outcome,
                        &mut path.facts,
                    );
                }
                if let Some(mask) = bit_field_mask {
                    for path in &mut paths {
                        if let ExpressionOutcome::Value(value) = &mut path.outcome
                            && let ProgramValue::UInt8(bits) = value.native().as_ref()
                        {
                            *value = ProgramValue::UInt8(super::byte_view::mask_byte(
                                bits.clone(),
                                mask,
                            ))
                            .into();
                        }
                    }
                }
                // A pointer read from memory designates an object of the
                // class its lvalue's type points to, unless it carries the
                // class of the declaration that formed it.
                if let Some(pointee) = lvalue.access_class().and_then(|class| class.pointee()) {
                    for path in &mut paths {
                        if let ExpressionOutcome::Value(value) = &mut path.outcome
                            && value.pointer().is_some()
                        {
                            *value = value.retain_checked_pointer(
                                value
                                    .native()
                                    .into_owned()
                                    .with_pointer_declared_object_class(Some(pointee.clone())),
                            );
                        }
                    }
                }
                if let Some(source) = source.and_then(|source| source.reference_access.as_ref())
                    && source.kind == crate::kernel::ReferenceAccessKind::Read
                {
                    let at = state.observation_point_id();
                    for path in &mut paths {
                        if matches!(path.outcome, ExpressionOutcome::Value(_)) {
                            let mut fact =
                                ExecutionPureFact::certified(Proposition::MemoryReadDefined {
                                    at,
                                    memory: state.memory.clone(),
                                    pointer: pointer.clone(),
                                    value_type: lvalue.value_type,
                                });
                            fact.public = false;
                            // This is a consequence of completing the read,
                            // never a condition selecting an evaluation path.
                            fact.logical_read_equation = true;
                            fact.reference_observation =
                                crate::kernel::source_access::ReferenceObservationSource::new(
                                    source.clone(),
                                    pointer.clone(),
                                    &state.memory,
                                    at,
                                    lvalue.value_type,
                                );
                            path.facts.push(fact);
                        }
                    }
                }
                if !lvalue.is_volatile() || SpecificationAccessScope::is_active() {
                    return Ok(paths
                        .into_iter()
                        .map(|path| {
                            path.map_value(|value| match value {
                                ExecutionValue::Native(value) => {
                                    ExecutionValue::retain_formed_pointer(value)
                                }
                                value => value,
                            })
                        })
                        .collect());
                }
                for path in &mut paths {
                    if let ExpressionOutcome::Value(value) = &path.outcome {
                        path.facts.push(volatile_access_fact(
                            budget,
                            VolatileAccessKind::Read,
                            pointer.clone(),
                            lvalue.value_type,
                            value.clone(),
                        )?);
                    }
                }
                paths
                    .into_iter()
                    .map(|path| {
                        path.map_value(|value| match value {
                            ExecutionValue::Native(value) => {
                                ExecutionValue::retain_formed_pointer(value)
                            }
                            value => value,
                        })
                    })
                    .collect()
            }
        },
        LValueOutcome::UndefinedBehavior(undefined_behavior) => vec![ExecutionValuePath {
            outcome: ExpressionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        }],
        LValueOutcome::RuntimeError(error) => vec![ExecutionValuePath {
            outcome: ExpressionOutcome::RuntimeError(error),
            facts,
            obligations,
        }],
    })
}

pub(in crate::kernel) fn address_of_lvalue_paths(
    state: &ExecutionState,
    target: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_program_lvalue_paths(state, target, assumptions, budget)? {
        paths.push(match lvalue_path.outcome {
            LValueOutcome::LValue(lvalue) => match lvalue.pointer(state) {
                Some(pointer) => {
                    // A struct object is stored as its byte array; its
                    // address is a struct pointer, which the C front end
                    // spells with the int32-pointer placeholder. Alignment
                    // of any declared object is intrinsic to its block,
                    // recorded when the block was created.
                    let is_aggregate = match &lvalue.storage {
                        LValueStorage::Local { name } => matches!(
                            state.locals.binding(name),
                            Some(LocalBinding::AggregateObject { .. })
                        ),
                        LValueStorage::Memory { .. } => matches!(target,
                            ProgramExpression::Variable(name) if name.static_id().and_then(|id| id.metadata())
                                .is_some_and(|metadata| metadata.aggregate && metadata.array_shape.is_none())),
                    };
                    let pointer_type = if is_aggregate {
                        Some(ProgramType::Int32Pointer)
                    } else {
                        // A byte-array lvalue can name a complete record's
                        // footprint for non-reading checked address formation.
                        // Its address is carried as a byte pointer; no array
                        // element or record field is loaded here.
                        match lvalue.value_type() {
                            ProgramType::UInt8Array(_) => Some(ProgramType::UInt8Pointer),
                            value_type => value_type.pointer_to(),
                        }
                    };
                    match pointer_type {
                        Some(pointer_type) => {
                            let facts = lvalue_path.facts;
                            let mut address = Pointer::new(pointer, pointer_type)
                                .with_pointee_volatile(lvalue.is_volatile())
                                .with_pointee_constant(lvalue.is_constant())
                                .with_bounds(lvalue.bounds().cloned());
                            if lvalue.bounds_known && lvalue.bounds().is_none() {
                                address = address.with_root_bounds();
                            }
                            if let Some(provenance) = &lvalue.provenance {
                                address = address
                                    .with_provenance(provenance.clone())
                                    .with_bounds_owner(lvalue.bounds_owner.clone());
                            }
                            let value = ProgramValue::Pointer(address);
                            ExpressionPath {
                                outcome: ExpressionOutcome::Value(value),
                                facts,
                                obligations: lvalue_path.obligations,
                            }
                        }
                        None => ExpressionPath {
                            outcome: ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                            facts: lvalue_path.facts,
                            obligations: lvalue_path.obligations,
                        },
                    }
                }
                None => ExpressionPath {
                    outcome: ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(
                        format!("{target:?}"),
                    )),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
                },
            },
            LValueOutcome::UndefinedBehavior(undefined_behavior) => ExpressionPath {
                outcome: ExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
            LValueOutcome::RuntimeError(error) => ExpressionPath {
                outcome: ExpressionOutcome::RuntimeError(error),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn is_external_memory_pointer(pointer: &Address) -> bool {
    !pointer.base.is_local_block()
        && !pointer.base.is_global_block()
        && !pointer.base.is_static_block()
        && !pointer.base.starts_with("string:")
        && !pointer.base.is_havoc_block()
}

pub(in crate::kernel) fn resolve_local_pointer_alias(
    state: &ExecutionState,
    pointer: &Address,
    assumptions: &PureFactContext,
) -> Address {
    state
        .locals
        .slots()
        .find(|slot| {
            **slot == *pointer
                || pointers_proven_equal_for_memory_resolution(pointer, slot, assumptions)
        })
        .cloned()
        .unwrap_or_else(|| pointer.clone())
}

pub(in crate::kernel) fn program_expression_pointee_type(
    state: &ExecutionState,
    expression: &ProgramExpression,
) -> Option<ProgramType> {
    match expression {
        ProgramExpression::Value(value) => value.program_type().pointee_type(),
        ProgramExpression::Variable(name) => match state.locals.binding(name) {
            Some(LocalBinding::Object { program_type, .. }) => program_type.pointee_type(),
            Some(LocalBinding::UninitializedObject { program_type, .. }) => {
                program_type.pointee_type()
            }
            Some(LocalBinding::GlobalObject { program_type, .. }) => program_type.pointee_type(),
            Some(LocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            Some(LocalBinding::AggregateObject { .. }) => Some(ProgramType::UInt8),
            None => name
                .static_id()
                .and_then(|id| id.metadata())
                .and_then(|metadata| {
                    if metadata.aggregate {
                        Some(ProgramType::UInt8)
                    } else {
                        metadata
                            .program_type
                            .array_element_type()
                            .or_else(|| metadata.program_type.pointee_type())
                    }
                }),
        },
        // A call's result has the callee's declared type.
        ProgramExpression::StringLiteral(identity) => state
            .literal_values
            .get(identity)?
            .program_type()
            .pointee_type(),
        ProgramExpression::StepResult { step, .. } => {
            state.step_result(*step)?.program_type().pointee_type()
        }
        ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
        ProgramExpression::AddressOf(target) | ProgramExpression::CheckedObjectAddress(target) => {
            program_expression_lvalue_type(state, target)
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            program_expression_pointee_type(state, pointer)
        }
        ProgramExpression::TypedLoad { value_type, .. } => match value_type {
            ProgramType::Int32Array(_) => Some(ProgramType::Int32),
            ProgramType::UInt8Array(_) => Some(ProgramType::UInt8),
            ProgramType::Int8Array(_) => Some(ProgramType::Int8),
            ProgramType::Int16Array(_) => Some(ProgramType::Int16),
            ProgramType::UInt16Array(_) => Some(ProgramType::UInt16),
            ProgramType::UInt32Array(_) => Some(ProgramType::UInt32),
            ProgramType::Int64Array(_) => Some(ProgramType::Int64),
            ProgramType::Int128Array(_) => Some(ProgramType::Int128),
            ProgramType::UInt64Array(_) => Some(ProgramType::UInt64),
            ProgramType::UInt128Array(_) => Some(ProgramType::UInt128),
            ProgramType::Float32Array(_) => Some(ProgramType::Float32),
            ProgramType::Float64Array(_) => Some(ProgramType::Float64),
            ProgramType::PointerArray(element, _) => Some(element.pointer_type()),
            value_type => value_type.pointee_type(),
        },
        ProgramExpression::Add(left, right) => program_expression_pointee_type(state, left)
            .or_else(|| program_expression_pointee_type(state, right)),
        ProgramExpression::Subtract(left, _) => program_expression_pointee_type(state, left),
        // An indexed pointer expression is itself the value stored in the
        // selected cell. For `slots[0]` where `slots` is `int32**`, the
        // lvalue type is `int32*`, so its pointee type is `int32`.
        ProgramExpression::Index(base, _) => {
            program_expression_pointee_type(state, base).and_then(ProgramType::pointee_type)
        }
        _ => None,
    }
}

pub(in crate::kernel) fn program_expression_lvalue_type(
    state: &ExecutionState,
    expression: &ProgramExpression,
) -> Option<ProgramType> {
    match expression {
        ProgramExpression::Variable(name) => state.locals.object_type(name).or_else(|| {
            let metadata = name.static_id()?.metadata()?;
            if metadata.aggregate && metadata.array_shape.is_none() {
                None
            } else {
                Some(
                    metadata
                        .program_type
                        .array_element_type()
                        .unwrap_or(metadata.program_type),
                )
            }
        }),
        ProgramExpression::Load(pointer) => program_expression_pointee_type(state, pointer),
        ProgramExpression::TypedLoad { value_type, .. } => Some(*value_type),
        ProgramExpression::Index(base, _) => program_expression_pointee_type(state, base),
        _ => None,
    }
}

pub(in crate::kernel) fn program_expression_pointer_step_width(
    state: &ExecutionState,
    expression: &ProgramExpression,
) -> Option<u32> {
    program_expression_pointee_type(state, expression).map(ProgramType::byte_width)
}

/// The C `int` a condition evaluates to: `1` when it holds, `0` when it does
/// not, one path per outcome the facts leave open.
pub(in crate::kernel) fn condition_as_program_int32_paths(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    condition_as_program_int32_paths_valued(condition, facts, obligations, assumptions, false)
}

/// [`condition_as_program_int32_paths`] for the condition's negation: `0` when it
/// holds, `1` when it does not.
pub(in crate::kernel) fn condition_as_program_int32_not_paths(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    condition_as_program_int32_paths_valued(condition, facts, obligations, assumptions, true)
}

pub(in crate::kernel) fn condition_as_program_int32_paths_valued(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    negated: bool,
) -> Vec<ExpressionPath> {
    let value = |holds: bool| int32(u32::from(holds != negated));
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(holds) => vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value(holds)),
            facts,
            obligations,
        }],
        // A Rust `Bool` value (decision D5) is the condition, as its cast.
        None if ConditionValueScope::is_active() => vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(ProgramValue::Int32(MachineTerm::bool_cast(
                MachineIntegerType::Int32,
                if negated {
                    ConditionTerm::bool_not(condition)
                } else {
                    condition
                },
            ))),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                ExpressionPath {
                    outcome: ExpressionOutcome::Value(value(true)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                ExpressionPath {
                    outcome: ExpressionOutcome::Value(value(false)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct TruthinessPath {
    pub(in crate::kernel) is_true: bool,
    pub(in crate::kernel) facts: ExecutionFacts,
    pub(in crate::kernel) obligations: Vec<ProofObligation>,
}

pub(in crate::kernel) fn program_truthiness_paths(
    value: ProgramValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<TruthinessPath> {
    match value.numeric_value().clone() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Parameter(_) => {
            unreachable!("abstract truthiness must be rejected by the caller")
        }
        ProgramValue::Void => unreachable!("void truthiness must be rejected by the caller"),
        // A `Bool` (Stage 5) is tested by its own condition, read through
        // its negations, so `if (b)` for `b = x` splits on `x == 0`.
        ProgramValue::Bool(bits) => {
            let Proposition::ConditionIs(condition, holds) =
                ConditionTerm::truth_of_bool_word(&bits).truth_claim(true)
            else {
                unreachable!("a truth claim is a condition claim");
            };
            match decide_with_facts(assumptions, &facts, condition.native_compat()) {
                Some(value) => vec![TruthinessPath {
                    is_true: value == holds,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(
                        &mut true_facts,
                        assumptions,
                        (condition.clone()).native_compat().clone(),
                        holds,
                    )
                    .expect("unknown bool truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(
                        &mut false_facts,
                        assumptions,
                        condition.native_compat().clone(),
                        !holds,
                    )
                    .expect("unknown bool truthiness fact should be consistent");
                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        ProgramValue::Int8(bits) => {
            let is_zero = ConditionTerm::equal(bits, MachineTerm::constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![TruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![TruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");

                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");

                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        ProgramValue::Int16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::UInt32(bits) => {
            let is_zero = ConditionTerm::equal(bits, MachineTerm::constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![TruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![TruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");

                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");

                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        ProgramValue::Int64(bits) => {
            let is_zero = ConditionTerm::int64_equal(bits, MachineTerm::int64_constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![TruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");
                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        ProgramValue::UInt64(bits) => {
            let is_zero = ConditionTerm::uint64_equal(bits, MachineTerm::uint64_constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![TruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");
                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        value @ (ProgramValue::Int128(_) | ProgramValue::UInt128(_)) => {
            let ty =
                MachineIntegerType::from_program_type(value.program_type()).expect("wide integer");
            let bits = match value {
                ProgramValue::Int128(bits) | ProgramValue::UInt128(bits) => bits,
                _ => unreachable!(),
            };
            let integer = IntegerTerm::from_machine(ty, bits).expect("typed wide integer");
            let is_zero = ConditionTerm::integer_equal(integer, IntegerTerm::constant(0.into()));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![TruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");
                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        ProgramValue::Float32(bits) => program_float_truthiness_paths(
            ConditionTerm::float32_classification(bits, FloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        ProgramValue::Float64(bits) => program_float_truthiness_paths(
            ConditionTerm::float64_classification(bits, FloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        ProgramValue::Pointer(pointer) => {
            let is_null = pointer_is_null_condition(pointer.address().clone());
            match decide_with_facts(assumptions, &facts, &is_null) {
                Some(true) => vec![TruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![TruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut nonnull_facts = facts.clone();
                    add_condition_path_fact(
                        &mut nonnull_facts,
                        assumptions,
                        is_null.clone(),
                        false,
                    )
                    .expect("unknown pointer truthiness fact should be consistent");

                    let mut null_facts = facts;
                    add_condition_path_fact(&mut null_facts, assumptions, is_null, true)
                        .expect("unknown pointer truthiness fact should be consistent");

                    vec![
                        TruthinessPath {
                            is_true: true,
                            facts: nonnull_facts,
                            obligations: obligations.clone(),
                        },
                        TruthinessPath {
                            is_true: false,
                            facts: null_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
    }
}

fn program_float_truthiness_paths(
    is_zero: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<TruthinessPath> {
    match decide_with_facts(assumptions, &facts, &is_zero) {
        Some(is_zero) => vec![TruthinessPath {
            is_true: !is_zero,
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                .expect("unknown floating truthiness fact should be consistent");
            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                .expect("unknown floating truthiness fact should be consistent");
            vec![
                TruthinessPath {
                    is_true: true,
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                TruthinessPath {
                    is_true: false,
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn program_truthiness_as_program_int32_paths(
    value: ProgramValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    program_truthiness_paths(value, facts, obligations, assumptions)
        .into_iter()
        .map(|path| ExpressionPath {
            outcome: ExpressionOutcome::Value(int32(if path.is_true { 1 } else { 0 })),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect()
}

#[cfg(test)]
mod pointer_integer_tests {
    use super::*;

    fn cast(
        value: ProgramValue,
        ty: ProgramType,
        context: &PureFactContext,
    ) -> Result<ProgramValue, RuntimeError> {
        let mut obligations = Vec::new();
        let result = cast_program_value_to_type_with_integer_origin(
            value,
            ty,
            IntegerConversion::Modular,
            &mut obligations,
            context,
            Some(Address::symbolic(Variable(991_099))),
        );
        assert!(obligations.is_empty());
        result
    }

    #[test]
    fn numeric_pointer_observation_retains_object_class_without_subobject_authority() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let root = Address::symbolic(Variable(991_085));
        let source = Pointer::new(root.clone(), ProgramType::Int32Pointer)
            .with_object_class(Some(class.clone()))
            .with_bounds(Some(SubobjectBounds {
                start: root,
                width: 4u32.into(),
            }));
        let context = PureFactContext::new();
        let encoded = cast(
            ProgramValue::Pointer(source.clone()),
            ProgramType::UInt64,
            &context,
        )
        .unwrap();
        let ProgramValue::Pointer(decoded) = cast(
            encoded.numeric_value().clone(),
            ProgramType::Float64Pointer,
            &context,
        )
        .unwrap() else {
            panic!("pointer cast")
        };
        assert_eq!(decoded.address(), source.address());
        assert_eq!(decoded.object_class(), Some(class));
        assert!(!decoded.bounds_are_known());
        assert_ne!(decoded.provenance(), source.provenance());
    }

    #[test]
    fn pointer_integer_round_trip_retains_the_complete_pointer() {
        let root = Pointer::new(
            Address::symbolic(Variable(991_001)),
            ProgramType::Int32Pointer,
        );
        let member = root.clone().with_bounds(Some(SubobjectBounds {
            start: root.address().clone(),
            width: 4u32.into(),
        }));
        let context = PureFactContext::new();
        for ty in [ProgramType::Int64, ProgramType::UInt64] {
            for pointer in [
                member.clone(),
                member
                    .clone()
                    .with_address(member.address().offset_by_bytes(4)),
            ] {
                let word = cast(ProgramValue::Pointer(pointer.clone()), ty, &context).unwrap();
                assert_eq!(
                    cast(word.clone(), ProgramType::Int32Pointer, &context).unwrap(),
                    ProgramValue::Pointer(pointer)
                );
                let ProgramValue::Pointer(opaque) = cast(
                    word.numeric_value().clone(),
                    ProgramType::Int32Pointer,
                    &context,
                )
                .unwrap() else {
                    panic!("pointer")
                };
                assert!(!opaque.bounds_are_known());
                assert_ne!(opaque.provenance(), member.provenance());
            }
        }
    }

    #[test]
    fn equal_integer_bits_do_not_exchange_pointer_bounds() {
        let root = Pointer::new(
            Address::symbolic(Variable(991_002)),
            ProgramType::Int32Pointer,
        );
        let member = root.clone().with_bounds(Some(SubobjectBounds {
            start: root.address().clone(),
            width: 4u32.into(),
        }));
        let context = PureFactContext::new();
        let root_word = cast(
            ProgramValue::Pointer(root.clone()),
            ProgramType::UInt64,
            &context,
        )
        .unwrap();
        let member_word = cast(
            ProgramValue::Pointer(member.clone()),
            ProgramType::UInt64,
            &context,
        )
        .unwrap();
        assert_eq!(root_word.numeric_value(), member_word.numeric_value());
        assert_ne!(root_word, member_word);
        assert_eq!(
            cast(root_word, ProgramType::Int32Pointer, &context).unwrap(),
            ProgramValue::Pointer(root.clone())
        );
        assert_eq!(
            cast(member_word.clone(), ProgramType::VoidPointer, &context).unwrap(),
            ProgramValue::Pointer(member.with_type(ProgramType::VoidPointer))
        );
        let variable = MachineTerm::Variable(Variable(991_003));
        let context = context.assume_condition(
            ConditionTerm::uint64_equal(
                variable.clone(),
                program_value_bitvector_term(&member_word).unwrap(),
            ),
            true,
        );
        let ProgramValue::Pointer(opaque) = cast(
            ProgramValue::UInt64(variable),
            ProgramType::Int32Pointer,
            &context,
        )
        .unwrap() else {
            panic!("pointer")
        };
        assert!(!opaque.bounds_are_known());
        assert!(!context.pointer_provenance_match(&opaque, &root));
    }
}

#[cfg(test)]
mod pointer_integer_partial_write_tests {
    use super::*;

    #[test]
    fn a_partial_byte_write_discards_the_representation_even_when_bits_are_unchanged() {
        let context = PureFactContext::new();
        let word = cast_program_value_to_type(
            ProgramValue::Pointer(Pointer::new(
                Address::symbolic(Variable(995_001)),
                ProgramType::Int32Pointer,
            )),
            ProgramType::UInt64,
            IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let byte = crate::kernel::eval::byte_view::integer_cell_byte(&word, 0).unwrap();
        let cell = crate::kernel::eval::byte_view::ContainingIntegerCell {
            pointer: Address::null(),
            value: word,
            byte: 0,
        };
        let updated = crate::kernel::eval::byte_view::integer_cell_with_byte(
            &cell,
            &ProgramValue::UInt8(byte),
        )
        .unwrap();
        assert!(matches!(updated, ProgramValue::UInt64(_)));
    }
}

#[cfg(test)]
mod pointer_integer_cast_identity_tests {
    use super::*;

    #[test]
    fn identical_numeric_bits_cannot_copy_a_casts_established_bounds() {
        let source = Pointer::new(
            Address::symbolic(Variable(997_001)),
            ProgramType::Int32Pointer,
        );
        let bits = MachineTerm::integer_address(source.address().clone());
        let context = PureFactContext::new();
        let cast = |origin| {
            cast_program_value_to_type_with_integer_origin(
                ProgramValue::UInt64(bits.clone()),
                ProgramType::Int32Pointer,
                IntegerConversion::Modular,
                &mut Vec::new(),
                &context,
                Some(Address::symbolic(Variable(origin))),
            )
            .unwrap()
        };
        let ProgramValue::Pointer(first) = cast(997_002) else {
            panic!("pointer")
        };
        let ProgramValue::Pointer(second) = cast(997_003) else {
            panic!("pointer")
        };
        assert_eq!(first.address(), second.address());
        let context =
            context.assume_condition(ConditionTerm::pointer_equal(first, source.clone()), true);
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::from_pointer_value(&source, 0u32.into(), 1u32.into(), 4),
        ));
        assert!(!resources.permits_designated_memory_read(
            second.address(),
            Some(second.access_provenance()),
            4,
            &context
        ));
    }
}

#[cfg(test)]
mod packed_word_contract_tests {
    use super::*;

    fn cast(value: ProgramValue, assumptions: &PureFactContext) -> Pointer {
        let result = cast_program_value_to_type(
            value,
            ProgramType::Int32Pointer,
            IntegerConversion::Modular,
            &mut Vec::new(),
            assumptions,
        )
        .unwrap();
        let ProgramValue::Pointer(pointer) = result else {
            panic!("pointer cast")
        };
        pointer
    }

    #[test]
    fn modulo_conversion_observes_bits_and_discards_the_word_carrier() {
        let word = ProgramValue::UInt64(MachineTerm::uint64_constant(4_294_967_297))
            .complete_word(Address::symbolic(Variable(997_030)));
        assert_eq!(
            crate::kernel::machine_integer::conversion::convert_value(
                word.clone(),
                MachineIntegerType::UInt32
            ),
            Some(ProgramValue::UInt32(MachineTerm::uint32_constant(1)))
        );
        assert_eq!(
            crate::kernel::machine_integer::conversion::convert_value(
                word,
                MachineIntegerType::UInt64
            ),
            Some(ProgramValue::UInt64(MachineTerm::uint64_constant(
                4_294_967_297
            )))
        );
    }

    #[test]
    fn complete_word_narrowing_uses_its_numeric_equality() {
        let bits = MachineTerm::Variable(Variable(997_020));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(bits.clone(), MachineTerm::uint64_constant(41)),
            true,
        );
        let word = ProgramValue::UInt64(bits).complete_word(Address::symbolic(Variable(997_021)));
        let narrowed =
            coerce_program_value_to_type(word, ProgramType::Int32, &mut Vec::new(), &context)
                .unwrap();
        let term = crate::kernel::spec::program_value_bitvector_term(&narrowed).unwrap();
        assert_eq!(
            context.decide(&ConditionTerm::equal(term, MachineTerm::constant(41))),
            Some(true)
        );
    }

    #[test]
    fn incoming_word_carriers_need_full_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let bits = MachineTerm::Variable(Variable(997_001));
        let word =
            ProgramValue::UInt64(bits.clone()).complete_word(Address::symbolic(Variable(997_002)));
        let other = ProgramValue::UInt64(bits).complete_word(Address::symbolic(Variable(997_003)));
        let empty = PureFactContext::new();
        let reconstructed = cast(word, &empty);
        let unrelated = cast(other, &empty);
        assert_eq!(reconstructed.address(), unrelated.address());
        assert!(!empty.pointer_provenance_match(&reconstructed, &unrelated));
        let target = Pointer::new(
            Address::symbolic(Variable(997_004)),
            ProgramType::Int32Pointer,
        )
        .with_bounds(Some(SubobjectBounds {
            start: Address::symbolic(Variable(997_004)),
            width: 4u32.into(),
        }));
        let numeric = empty.assume_condition(
            ConditionTerm::address_equal(reconstructed.address().clone(), target.address().clone()),
            true,
        );
        assert!(!numeric.pointer_provenance_match(&reconstructed, &target));
        let relation = Proposition::condition_is(
            ConditionTerm::PointerEqual(Box::new(reconstructed.clone()), Box::new(target.clone())),
            true,
        );
        let full = numeric.assume_proposition(relation.clone());
        assert!(full.pointer_provenance_match(&reconstructed, &target));
        assert!(!full.pointer_provenance_match(&unrelated, &target));
    }

    #[test]
    fn modified_incoming_word_tag_bits_must_be_cleared_before_casting() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let word = ProgramValue::UInt64(MachineTerm::Variable(Variable(997_010)))
            .complete_word(Address::symbolic(Variable(997_011)));
        let original = cast(word.clone(), &context);
        let value_of = |paths: Vec<ExpressionPath>| {
            let [path] = paths.as_slice() else {
                panic!("one scalar result")
            };
            let ExpressionOutcome::Value(value) = &path.outcome else {
                panic!("value")
            };
            value.clone()
        };
        let tagged = value_of(super::super::operators::apply_program_bitwise_binary(
            word,
            ProgramValue::Int32(MachineTerm::constant(1)),
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            super::super::operators::BitwiseOperation::Or,
        ));
        assert!(
            cast_program_value_to_type(
                tagged.clone(),
                ProgramType::Int32Pointer,
                IntegerConversion::Modular,
                &mut Vec::new(),
                &context
            )
            .is_err()
        );
        let cleared = value_of(super::super::operators::apply_program_bitwise_binary(
            tagged,
            ProgramValue::Int32(MachineTerm::constant(!1)),
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            super::super::operators::BitwiseOperation::And,
        ));
        let restored = cast(cleared, &context);
        assert!(context.pointer_provenance_match(&restored, &original));
        assert!(!restored.bounds_are_known());
    }
}

/// Whether the held resources permit reading the local at `pointer` whole:
/// one element of its type's width, or, for a type of unknown size, its
/// whole object.
fn local_read_permitted(
    state: &ExecutionState,
    pointer: &Address,
    value_type: ProgramType,
    assumptions: &PureFactContext,
) -> bool {
    match value_type {
        ProgramType::Parameter(parameter) if parameter.has_abstract_size() => {
            state.resources().permits_object_access(
                &MemoryRange::access(pointer.clone(), value_type),
                false,
                assumptions,
            )
        }
        _ => resource_context_has_read(
            state.resources(),
            pointer,
            value_type.byte_width(),
            assumptions,
        ),
    }
}
