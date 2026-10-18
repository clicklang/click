use super::*;
use crate::kernel::effective_type::CAccessClass;

fn integer_to_float_bits(
    negative: bool,
    magnitude: u128,
    fraction_bits: u32,
    exponent_bits: u32,
    bias: i32,
    sign_bit: u64,
) -> u64 {
    let sign = if negative { sign_bit } else { 0 };
    if magnitude == 0 {
        return sign;
    }

    let precision = fraction_bits + 1;
    let highest_bit = 127 - magnitude.leading_zeros();
    let mut exponent = highest_bit as i32;
    let mut significand = if highest_bit < precision - 1 {
        magnitude << (precision - 1 - highest_bit)
    } else {
        crate::kernel::primitives::round_right_to_even(magnitude, highest_bit - (precision - 1))
    };

    if significand == 1u128 << precision {
        significand >>= 1;
        exponent += 1;
    }

    let exponent_limit = (1u32 << exponent_bits) - 1;
    let encoded_exponent = exponent + bias;
    if encoded_exponent >= exponent_limit as i32 {
        return sign | (u64::from(exponent_limit) << fraction_bits);
    }

    sign | ((encoded_exponent as u64) << fraction_bits)
        | ((significand as u64) & ((1u64 << fraction_bits) - 1))
}

fn integer_to_float32_bits(negative: bool, magnitude: u128) -> u32 {
    integer_to_float_bits(negative, magnitude, 23, 8, 127, 0x8000_0000) as u32
}

fn integer_to_float64_bits(negative: bool, magnitude: u128) -> u64 {
    integer_to_float_bits(negative, magnitude, 52, 11, 1023, 0x8000_0000_0000_0000)
}

fn float32_to_float64_bits(bits: u32) -> u64 {
    let sign = u64::from(bits & 0x8000_0000) << 32;
    let exponent = (bits >> 23) & 0xff;
    let fraction = bits & 0x007f_ffff;
    if exponent == 0xff {
        // An infinity widens to an infinity of the same sign. A NaN keeps its
        // payload, which cannot vanish under the shift because a nonzero
        // binary32 fraction stays nonzero in the wider fraction field.
        if fraction == 0 {
            return sign | (0x7ffu64 << 52);
        }
        return sign | (0x7ffu64 << 52) | (u64::from(fraction) << 29);
    }
    if exponent != 0 {
        return sign | (u64::from(exponent + 1023 - 127) << 52) | (u64::from(fraction) << 29);
    }
    if fraction == 0 {
        return sign;
    }

    let highest_bit = 31 - fraction.leading_zeros();
    let unbiased_exponent = highest_bit as i32 - 149;
    let encoded_exponent = (unbiased_exponent + 1023) as u64;
    let significand = fraction ^ (1u32 << highest_bit);
    sign | (encoded_exponent << 52) | (u64::from(significand) << (52 - highest_bit))
}

fn float64_to_float32_bits(bits: u64) -> u32 {
    let sign = (bits >> 32) as u32 & 0x8000_0000;
    let exponent = ((bits >> 52) & 0x7ff) as u32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    if exponent == 0x7ff {
        return sign
            | if fraction == 0 {
                0x7f80_0000
            } else {
                0x7fc0_0000
            };
    }
    if exponent == 0 && fraction == 0 {
        return sign;
    }

    let (significand, base, highest_bit) = if exponent == 0 {
        let highest_bit = 63 - fraction.leading_zeros();
        (u128::from(fraction), -1074i32, highest_bit)
    } else {
        let significand = (1u128 << 52) | u128::from(fraction);
        let highest_bit = 52;
        (significand, exponent as i32 - 1023 - 52, highest_bit)
    };
    let top_exponent = highest_bit as i32 + base;

    if top_exponent >= -126 {
        let shift = (top_exponent - 23 - base) as u32;
        let mut rounded = crate::kernel::primitives::round_right_to_even(significand, shift);
        let mut exponent = top_exponent;
        if rounded == 1u128 << 24 {
            rounded >>= 1;
            exponent += 1;
        }
        if exponent > 127 {
            return sign | 0x7f80_0000;
        }
        return sign | (((exponent + 127) as u32) << 23) | ((rounded as u32) & 0x007f_ffff);
    }

    let shift = (-149 - base) as u32;
    let rounded = crate::kernel::primitives::round_right_to_even(significand, shift);
    if rounded >= 1u128 << 23 {
        sign | 0x0080_0000
    } else {
        sign | rounded as u32
    }
}

fn integer_constant_as_sign_magnitude(value: &CValue) -> Option<(bool, u128)> {
    match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Bool(bits) => Some((false, u128::from(bits.as_const()?))),
        CValue::Int8(bits) => {
            let value = bits.as_const()? as i32;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        CValue::Int16(bits) | CValue::Int32(bits) => {
            let value = bits.as_const()? as i32;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        CValue::UInt8(bits) | CValue::UInt16(bits) | CValue::UInt32(bits) => {
            Some((false, u128::from(bits.as_const()?)))
        }
        CValue::Int64(bits) => {
            let value = bits.int64_as_const()?;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        CValue::UInt64(bits) => Some((false, u128::from(bits.uint64_as_const()?))),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Float32(_)
        | CValue::Float64(_)
        | CValue::Pointer(_) => None,
    }
}

fn float_significand_as_integer(
    negative: bool,
    exponent: u32,
    fraction: u64,
    fraction_bits: u32,
    exponent_bits: u32,
    bias: i32,
) -> Option<(bool, u128)> {
    let exponent_limit = (1u32 << exponent_bits) - 1;
    if exponent == exponent_limit {
        return None;
    }
    let (significand, base) = if exponent == 0 {
        (u128::from(fraction), 1 - bias - fraction_bits as i32)
    } else {
        (
            (1u128 << fraction_bits) | u128::from(fraction),
            exponent as i32 - bias - fraction_bits as i32,
        )
    };
    let magnitude = if base >= 0 {
        // `checked_shl` only rejects a shift count of 128 or more; it drops
        // any bits carried off the top, which would turn a value too large
        // for the container into a small in-range magnitude. A value that
        // does not fit has no integer conversion at all, which is the same
        // answer the range check below gives for a merely out-of-range one.
        let shift = base as u32;
        if shift >= 128 || significand.leading_zeros() < shift {
            return None;
        }
        significand << shift
    } else if (-base) >= 128 {
        0
    } else {
        significand >> (-base as u32)
    };
    Some((negative && magnitude != 0, magnitude))
}

fn float_to_integer_value(negative: bool, magnitude: u128, target_type: CType) -> Option<CValue> {
    let signed_limit = |bits: u32| (1i128 << (bits - 1)) - 1;
    let (signed, bits) = match target_type {
        CType::Int8 => (true, 8),
        CType::Int16 => (true, 16),
        CType::Int32 => (true, 32),
        CType::Int64 => (true, 64),
        CType::UInt8 => (false, 8),
        CType::UInt16 => (false, 16),
        CType::UInt32 => (false, 32),
        CType::UInt64 => (false, 64),
        _ => return None,
    };
    if signed {
        let limit = signed_limit(bits) as u128;
        let negative_limit = limit + 1;
        if magnitude > if negative { negative_limit } else { limit } {
            return None;
        }
        let value = if negative {
            -(magnitude as i128)
        } else {
            magnitude as i128
        };
        return Some(match target_type {
            CType::Int8 => CValue::Int8(Bitvector32Term::Constant(value as i32 as u32)),
            CType::Int16 => CValue::Int16(Bitvector32Term::Constant(value as i32 as u32)),
            CType::Int32 => CValue::Int32(Bitvector32Term::Constant(value as i32 as u32)),
            CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(value as i64)),
            _ => unreachable!(),
        });
    }
    if negative && magnitude != 0 {
        return None;
    }
    let limit = (1u128 << bits) - 1;
    if magnitude > limit {
        return None;
    }
    let value = magnitude as u64;
    Some(match target_type {
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Constant(value as u32)),
        CType::UInt16 => CValue::UInt16(Bitvector32Term::Constant(value as u32)),
        CType::UInt32 => CValue::UInt32(Bitvector32Term::Constant(value as u32)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(value)),
        _ => unreachable!(),
    })
}

fn float32_to_integer_value(bits: u32, target_type: CType) -> Option<CValue> {
    let negative = bits & 0x8000_0000 != 0;
    let exponent = (bits >> 23) & 0xff;
    let fraction = u64::from(bits & 0x007f_ffff);
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 23, 8, 127)?;
    float_to_integer_value(negative, magnitude, target_type)
}

fn float64_to_integer_value(bits: u64, target_type: CType) -> Option<CValue> {
    let negative = bits & (1u64 << 63) != 0;
    let exponent = ((bits >> 52) & 0x7ff) as u32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 52, 11, 1023)?;
    float_to_integer_value(negative, magnitude, target_type)
}

fn integer_to_float_value(value: CValue, target_type: CType) -> Option<CValue> {
    let (source_name, term) = match value.numeric_value() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Bool(term) => ("bool", term),
        CValue::Int8(term) => ("int8", term),
        CValue::Int16(term) => ("int16", term),
        CValue::Int32(term) => ("int32", term),
        CValue::UInt8(term) => ("uint8", term),
        CValue::UInt16(term) => ("uint16", term),
        CValue::UInt32(term) => ("uint32", term),
        CValue::Int64(term) => ("int64", term),
        CValue::UInt64(term) => ("uint64", term),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Float32(_)
        | CValue::Float64(_)
        | CValue::Pointer(_) => return None,
    };
    let target_name = match target_type {
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        _ => return None,
    };
    if let Some((negative, magnitude)) = integer_constant_as_sign_magnitude(&value) {
        return Some(match target_type {
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(integer_to_float32_bits(
                negative, magnitude,
            ))),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(
                integer_to_float64_bits(negative, magnitude),
            )),
            _ => unreachable!(),
        });
    }
    let term = Bitvector32Term::opaque_conversion(
        format!("c_{source_name}_to_{target_name}"),
        term.clone(),
    );
    Some(match target_type {
        CType::Float32 => CValue::Float32(term),
        CType::Float64 => CValue::Float64(term),
        _ => unreachable!(),
    })
}

fn float_integer_bound_bits(
    source_type: CType,
    exponent: u32,
    negative: bool,
) -> Option<Bitvector32Term> {
    let magnitude = 1u128.checked_shl(exponent)?;
    Some(match source_type {
        CType::Float32 => Bitvector32Term::Constant(integer_to_float32_bits(negative, magnitude)),
        CType::Float64 => {
            Bitvector32Term::UInt64Constant(integer_to_float64_bits(negative, magnitude))
        }
        _ => return None,
    })
}

fn add_float_to_integer_obligations(
    value: &Bitvector32Term,
    source_type: CType,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<()> {
    let (signed, bits) = match target_type {
        CType::Int8 => (true, 8),
        CType::Int16 => (true, 16),
        CType::Int32 => (true, 32),
        CType::Int64 => (true, 64),
        CType::UInt8 => (false, 8),
        CType::UInt16 => (false, 16),
        CType::UInt32 => (false, 32),
        CType::UInt64 => (false, 64),
        _ => return None,
    };
    let finite = match source_type {
        CType::Float32 => {
            ConditionTerm::float32_classification(value.clone(), CFloatClassification::Finite)
        }
        CType::Float64 => {
            ConditionTerm::float64_classification(value.clone(), CFloatClassification::Finite)
        }
        _ => return None,
    };
    add_proof_obligation(
        obligations,
        assumptions,
        Proposition::ConditionIs(finite, true),
    )?;

    if signed {
        let lower = float_integer_bound_bits(source_type, bits - 1, true)?;
        let upper = float_integer_bound_bits(source_type, bits - 1, false)?;
        let lower = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                lower,
                CComparisonOperator::GreaterEqual,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                lower,
                CComparisonOperator::GreaterEqual,
            ),
            _ => unreachable!(),
        };
        let upper = match source_type {
            CType::Float32 => {
                ConditionTerm::float32_compare(value.clone(), upper, CComparisonOperator::LessThan)
            }
            CType::Float64 => {
                ConditionTerm::float64_compare(value.clone(), upper, CComparisonOperator::LessThan)
            }
            _ => unreachable!(),
        };
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(lower, true),
        )?;
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(upper, true),
        )?;
    } else {
        let lower = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                Bitvector32Term::Constant(0),
                CComparisonOperator::GreaterEqual,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                Bitvector32Term::UInt64Constant(0),
                CComparisonOperator::GreaterEqual,
            ),
            _ => unreachable!(),
        };
        let upper_bits = float_integer_bound_bits(source_type, bits, false)?;
        let upper = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                upper_bits,
                CComparisonOperator::LessThan,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                upper_bits,
                CComparisonOperator::LessThan,
            ),
            _ => unreachable!(),
        };
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(lower, true),
        )?;
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(upper, true),
        )?;
    }
    Some(())
}

fn float_to_integer_conversion_value(
    value: Bitvector32Term,
    source_type: CType,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    add_float_to_integer_obligations(&value, source_type, target_type, obligations, assumptions)?;
    let source_name = match source_type {
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        _ => return None,
    };
    let target_name = match target_type {
        CType::Int8 => "int8",
        CType::Int16 => "int16",
        CType::Int32 => "int32",
        CType::UInt8 => "uint8",
        CType::UInt16 => "uint16",
        CType::UInt32 => "uint32",
        CType::Int64 => "int64",
        CType::UInt64 => "uint64",
        _ => return None,
    };
    let term =
        Bitvector32Term::opaque_conversion(format!("c_{source_name}_to_{target_name}"), value);
    Some(match target_type {
        CType::Int8 => CValue::Int8(term),
        CType::Int16 => CValue::Int16(term),
        CType::Int32 => CValue::Int32(term),
        CType::UInt8 => CValue::UInt8(term),
        CType::UInt16 => CValue::UInt16(term),
        CType::UInt32 => CValue::UInt32(term),
        CType::Int64 => CValue::Int64(term),
        CType::UInt64 => CValue::UInt64(term),
        _ => unreachable!(),
    })
}

pub(in crate::kernel) fn evaluate_c_expression(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<CExpressionOutcome> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget).ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.obligations.is_empty() {
        return None;
    }
    Some(path.outcome)
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

/// Files the type range of a narrow integer value where the value is
/// produced, as certified path facts. The facts are the ones
/// [`crate::kernel::c_narrow_integer_range_facts`] states, so a parameter's
/// entry facts and a read value's path facts are one definition.
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
    value: &CValue,
) {
    if SPECIFICATION_READS.with(|depth| depth.get() > 0) {
        return;
    }
    let Some(range_facts) = crate::kernel::c_narrow_integer_range_facts(value) else {
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

pub(in crate::kernel) fn promote_c_int32_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value.numeric_value().clone() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int128(_) | CValue::UInt128(_) => None,

        CValue::Void => None,
        CValue::Bool(value) => Some(value),
        CValue::Int32(value) => Some(value),
        CValue::Int8(value) => Some(value),
        CValue::Int16(value) => Some(value),
        CValue::UInt8(value) => Some(value),
        CValue::UInt16(value) => Some(value),
        CValue::UInt32(_) | CValue::Int64(_) | CValue::UInt64(_) => None,
        CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_uint32_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value.numeric_value().clone() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Bool(value) | CValue::Int32(value) | CValue::UInt32(value) => Some(value),
        CValue::Int8(value) => Some(value),
        CValue::Int16(value) => Some(value),
        CValue::UInt8(value) => Some(value),
        CValue::UInt16(value) => Some(value),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_int64_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value.numeric_value().clone() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Int64(value) => Some(value),
        CValue::Bool(value) => Some(Bitvector32Term::int64_from_32(value)),
        CValue::Int8(value) => Some(Bitvector32Term::int64_from_32(value)),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::int64_from_32(value)),
        CValue::UInt32(value) => Some(Bitvector32Term::int64_from_uint32(value)),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_uint64_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value.numeric_value().clone() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::UInt64(value) => Some(value),
        CValue::Bool(value) => Some(Bitvector32Term::uint64_from_32(value)),
        CValue::UInt8(value) | CValue::UInt16(value) | CValue::UInt32(value) => {
            Some(Bitvector32Term::uint64_from_32(value))
        }
        CValue::Int8(value) => Some(Bitvector32Term::uint64_from_int32(value)),
        CValue::Int16(value) | CValue::Int32(value) => {
            Some(Bitvector32Term::uint64_from_int32(value))
        }
        CValue::Int64(value) => Some(Bitvector32Term::uint64_from_int64(value)),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
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

/// Converts a C value at an implicit conversion boundary, by C's rule.
pub(in crate::kernel) fn coerce_c_value_to_type(
    value: CValue,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    coerce_c_value_to_type_as(
        value,
        target_type,
        IntegerConversion::Modular,
        obligations,
        assumptions,
    )
}

pub(in crate::kernel) fn coerce_c_value_to_type_as(
    value: CValue,
    target_type: CType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // Assignment and argument binding preserve complete, unchanged words.
    // Every other numeric conversion starts from a mathematical observation.
    if matches!(value, CValue::PointerInteger(_)) && value.c_type() == target_type {
        return Some(value);
    }
    let value = value.numeric_value().clone();
    if target_type == CType::Bool && matches!(value.c_type(), CType::Int128 | CType::UInt128) {
        let source = MachineIntegerType::from_c_type(value.c_type())?;
        let observed = IntegerTerm::from_machine(source, c_value_bitvector_term(&value)?)?;
        return Some(CValue::Bool(Bitvector32Term::if_then_else(
            ConditionTerm::integer_equal(observed, IntegerTerm::constant_i64(0)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )));
    }
    if matches!(value.c_type(), CType::Int128 | CType::UInt128)
        || matches!(target_type, CType::Int128 | CType::UInt128)
    {
        let destination = MachineIntegerType::from_c_type(target_type)?;
        let source = if matches!(value, CValue::Bool(_)) {
            MachineIntegerType::UInt8
        } else {
            MachineIntegerType::from_c_type(value.c_type())?
        };
        // C's conversion is modulo 2^N for a signed destination too; a
        // specification's owes the signed range. An unsigned destination is
        // modulo 2^N under both.
        if conversion == IntegerConversion::Checked
            && destination.format().is_signed()
            && !destination.format().contains(source.format())
        {
            let observed = IntegerTerm::from_machine(source, c_value_bitvector_term(&value)?)?;
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
        return destination.convert_modulo_value(value);
    }
    if let Some(value) = coerce_c_null_pointer_constant(value.clone(), target_type) {
        return Some(value);
    }

    if matches!(target_type, CType::FunctionPointer(_))
        && let CValue::Pointer(pointer) = &value
        && pointer.c_type() == target_type
    {
        return Some(value);
    }

    // A direct function address starts with the intentionally untyped
    // unspecified signature marker. Call arguments retag it from the declared
    // parameter type before binding; typed stores need the same destination
    // context so a callback field can be initialized without weakening
    // already-typed function-pointer compatibility checks.
    if let (CType::FunctionPointer(signature), CValue::Pointer(pointer)) = (target_type, &value)
        && pointer.block.is_function()
        && pointer.c_type() == CType::FunctionPointer(CallbackSignature::UNSPECIFIED)
    {
        return Some(CValue::typed_pointer(
            pointer.pointer().clone(),
            CType::FunctionPointer(signature),
        ));
    }

    match (target_type, value) {
        (CType::Bool, CValue::Bool(value)) => Some(CValue::Bool(value)),
        (CType::Bool, crate::kernel::integer32_c_value!(value)) => {
            Some(CValue::Bool(Bitvector32Term::if_then_else(
                ConditionTerm::equal(value, Bitvector32Term::Constant(0)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )))
        }
        (CType::Bool, CValue::Int64(value)) => Some(CValue::Bool(Bitvector32Term::if_then_else(
            ConditionTerm::int64_equal(value, Bitvector32Term::Int64Constant(0)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ))),
        (CType::Bool, CValue::UInt64(value)) => Some(CValue::Bool(Bitvector32Term::if_then_else(
            ConditionTerm::uint64_equal(value, Bitvector32Term::UInt64Constant(0)),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ))),
        (CType::Bool, CValue::Pointer(pointer)) => {
            Some(CValue::Bool(Bitvector32Term::if_then_else(
                pointer_is_null_condition(pointer.into_pointer()),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )))
        }
        (CType::Int32, CValue::Bool(value)) => Some(CValue::Int32(value)),
        (CType::UInt32, CValue::Bool(value)) => Some(CValue::UInt32(value)),
        (CType::Int8, CValue::Bool(value)) => Some(CValue::Int8(value)),
        (CType::Int16, CValue::Bool(value)) => Some(CValue::Int16(value)),
        (CType::UInt8, CValue::Bool(value)) => Some(CValue::UInt8(value)),
        (CType::UInt16, CValue::Bool(value)) => Some(CValue::UInt16(value)),
        (CType::Int64, CValue::Bool(value)) => {
            Some(CValue::Int64(Bitvector32Term::int64_from_32(value)))
        }
        (CType::UInt64, CValue::Bool(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_32(value)))
        }
        (
            CType::Int32,
            CValue::Int8(value)
            | CValue::Int16(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value),
        ) => Some(CValue::Int32(value)),
        (CType::Int32, CValue::UInt32(value)) => Some(CValue::Int32(value)),
        (CType::UInt32, CValue::Int64(value) | CValue::UInt64(value)) => {
            Some(CValue::UInt32(Bitvector32Term::uint32_from_64(value)))
        }
        (CType::Int32, value @ (CValue::Int64(_) | CValue::UInt64(_))) => {
            narrow_integer(value, target_type, conversion, obligations, assumptions)
        }
        (CType::UInt32, crate::kernel::int_promoted_c_value!(value)) => Some(CValue::UInt32(value)),
        (CType::Int16, CValue::Int8(value) | CValue::UInt8(value)) => Some(CValue::Int16(value)),
        (CType::UInt16, CValue::UInt8(value)) => Some(CValue::UInt16(value)),
        (
            target @ (CType::Int8 | CType::UInt8 | CType::Int16 | CType::UInt16),
            value @ (CValue::Int8(_)
            | CValue::UInt8(_)
            | CValue::Int16(_)
            | CValue::UInt16(_)
            | CValue::Int32(_)
            | CValue::UInt32(_)
            | CValue::Int64(_)
            | CValue::UInt64(_)),
        ) => narrow_integer(value, target, conversion, obligations, assumptions),
        (CType::Int64, value @ CValue::UInt64(_)) => {
            narrow_integer(value, target_type, conversion, obligations, assumptions)
        }
        (CType::Int64, CValue::Int64(value)) => Some(CValue::Int64(value)),
        (CType::Int64, crate::kernel::int_promoted_c_value!(value)) => {
            Some(CValue::Int64(Bitvector32Term::int64_from_32(value)))
        }
        (CType::Int64, CValue::UInt32(value)) => {
            Some(CValue::Int64(Bitvector32Term::int64_from_uint32(value)))
        }
        (CType::UInt64, CValue::UInt64(value)) => Some(CValue::UInt64(value)),
        (CType::UInt64, CValue::Int64(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_int64(value)))
        }
        (CType::UInt64, crate::kernel::int_promoted_c_value!(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_int32(value)))
        }
        (CType::UInt64, CValue::UInt32(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_32(value)))
        }
        (CType::Float32, CValue::Float32(value)) => Some(CValue::Float32(value)),
        (CType::Float32, CValue::Float64(value)) => {
            let converted = value
                .float64_as_const()
                .map(|value| Bitvector32Term::Constant(float64_to_float32_bits(value)))
                .unwrap_or_else(|| {
                    Bitvector32Term::opaque_conversion("c_float64_to_float32", value)
                });
            Some(CValue::Float32(converted))
        }
        (CType::Float64, CValue::Float64(value)) => Some(CValue::Float64(value)),
        (CType::Float64, CValue::Float32(value)) => {
            let converted = value
                .float32_as_const()
                .map(|value| Bitvector32Term::UInt64Constant(float32_to_float64_bits(value)))
                .unwrap_or_else(|| {
                    Bitvector32Term::opaque_conversion("c_float32_to_float64", value)
                });
            Some(CValue::Float64(converted))
        }
        (
            target @ (CType::Float32 | CType::Float64),
            value @ (crate::kernel::integer64_c_value!(_)),
        ) => integer_to_float_value(value, target),
        (
            target @ (CType::Int8
            | CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64),
            CValue::Float32(value),
        ) => {
            if let Some(bits) = value.float32_as_const() {
                float32_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    CType::Float32,
                    target,
                    obligations,
                    assumptions,
                )
            }
        }
        (
            target @ (CType::Int8
            | CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64),
            CValue::Float64(value),
        ) => {
            if let Some(bits) = value.float64_as_const() {
                float64_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    CType::Float64,
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
/// one-byte-one-name signed read of that byte, `Bitvector32Term::signed_byte`.
/// Into `int32` the low word already is the value modulo 2^32, and into
/// `int64` the same 64 bits read as signed.
///
/// A specification's conversion ([`IntegerConversion::Checked`]) files the
/// same range conditions as obligations and is then the carrier itself.
fn narrow_integer(
    value: CValue,
    target: CType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let destination = MachineIntegerType::from_c_type(target)?;
    let term = match value {
        crate::kernel::integer_c_value!(term) => term,
        _ => return None,
    };
    let checked = conversion == IntegerConversion::Checked;
    match destination {
        MachineIntegerType::Int32 => {
            if checked {
                let bounds = if source == MachineIntegerType::UInt64 {
                    vec![(
                        ConditionTerm::Bitvector64UnsignedLessEqual(
                            term.clone().into(),
                            Bitvector32Term::UInt64Constant(i32::MAX as u64).into(),
                        ),
                        "int32 narrowing upper bound",
                    )]
                } else {
                    vec![
                        (
                            ConditionTerm::Bitvector64SignedGreaterEqual(
                                term.clone().into(),
                                Bitvector32Term::Int64Constant(i64::from(i32::MIN)).into(),
                            ),
                            "int32 narrowing lower bound",
                        ),
                        (
                            ConditionTerm::Bitvector64SignedLessEqual(
                                term.clone().into(),
                                Bitvector32Term::Int64Constant(i64::from(i32::MAX)).into(),
                            ),
                            "int32 narrowing upper bound",
                        ),
                    ]
                };
                for (condition, context) in bounds {
                    add_narrowing_bound_obligation(obligations, assumptions, condition, context)?;
                }
            }
            Some(CValue::Int32(Bitvector32Term::uint32_from_64(term)))
        }
        MachineIntegerType::Int64 => {
            if checked {
                add_narrowing_bound_obligation(
                    obligations,
                    assumptions,
                    ConditionTerm::Bitvector64UnsignedLessEqual(
                        term.clone().into(),
                        Bitvector32Term::UInt64Constant(i64::MAX as u64).into(),
                    ),
                    "int64 narrowing upper bound",
                )?;
            }
            Some(CValue::Int64(Bitvector32Term::int64_from_uint64_bits(term)))
        }
        _ if source == destination => Some(destination.value_from_term(term)),
        // The node is the same whatever the context knows, so a smart search
        // and the checked trace of its steps produce one term; the identity
        // inside the range is reasoning (`narrowed_cast_identity`), never a
        // context-dependent choice of representation here.
        _ if !checked => Some(
            destination.value_from_term(Bitvector32Term::machine_integer_cast(
                source,
                destination,
                term,
            )),
        ),
        _ => {
            let (bounds, carrier) =
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
            Some(destination.value_from_term(carrier))
        }
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
        Proposition::ConditionIs(condition.clone(), true),
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

pub(in crate::kernel) fn cast_c_value_to_type(
    value: CValue,
    target_type: CType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Result<CValue, CRuntimeError> {
    cast_c_value_to_type_with_integer_origin(
        value,
        target_type,
        conversion,
        obligations,
        assumptions,
        None,
    )
}

fn cast_c_value_to_type_with_integer_origin(
    value: CValue,
    target_type: CType,
    conversion: IntegerConversion,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    integer_pointer_origin: Option<Pointer>,
) -> Result<CValue, CRuntimeError> {
    if target_type.is_pointer() {
        match value {
            CValue::PointerInteger(record) if !matches!(target_type, CType::FunctionPointer(_)) => {
                // Numeric observations cannot choose the representation carrier.
                // A checked tagged value must have its tag removed before use.
                let pointer = match record.kind {
                    PointerIntegerKind::Exact => *record.pointer,
                    PointerIntegerKind::Word { changed_bits } => {
                        if changed_bits != 0 {
                            return Err(CRuntimeError::PointerConversion(
                                "integer-to-pointer cast requires modified tag bits cleared".into(),
                            ));
                        }
                        let bits = crate::kernel::spec::c_value_bitvector_term(&record.numeric)
                            .ok_or(CRuntimeError::TypeMismatch)?;
                        // A logical cast must name the same value before its
                        // own relationship is assumed. Numeric address choices
                        // belong to execution, never to this carrier's name.
                        record.pointer.with_address(Pointer::integer_address(bits))
                    }
                    PointerIntegerKind::Tagged => {
                        let bits = crate::kernel::spec::c_value_bitvector_term(&record.numeric)
                            .ok_or(CRuntimeError::TypeMismatch)?;
                        let recovered = super::pointer_tags::cast_tagged_address_to_pointer(
                            &bits,
                            assumptions,
                            obligations,
                            target_type,
                        )
                        .map_err(CRuntimeError::PointerConversion)?;
                        if recovered.as_ref().map(CPointerValue::pointer)
                            != Some(record.pointer.pointer())
                        {
                            return Err(CRuntimeError::PointerConversion(
                                "integer-to-pointer cast requires the original pointer with its tag cleared".into(),
                            ));
                        }
                        *record.pointer
                    }
                };
                return Ok(CValue::Pointer(pointer.with_type(target_type)));
            }
            CValue::Pointer(pointer) => {
                // Character-to-character casts retain the selected byte view.
                // Other casts to bytes, and every void cast, widen that view.
                let byte_to_byte =
                    matches!(pointer.c_type(), CType::UInt8Pointer | CType::Int8Pointer)
                        && matches!(target_type, CType::UInt8Pointer | CType::Int8Pointer);
                let pointer = pointer.with_type(target_type);
                return Ok(CValue::Pointer(
                    if !byte_to_byte
                        && matches!(
                            target_type,
                            CType::VoidPointer | CType::UInt8Pointer | CType::Int8Pointer
                        )
                    {
                        pointer.with_root_extent()
                    } else {
                        pointer
                    },
                ));
            }
            // An address without a complete representation record reconstructs
            // an opaque designation. Numeric facts cannot supply pointer bounds.
            CValue::UInt64(term) | CValue::Int64(term)
                if !matches!(target_type, CType::FunctionPointer(_)) =>
            {
                if term.uint64_as_const() == Some(0)
                    || assumptions.decide(&ConditionTerm::uint64_equal(
                        term.clone(),
                        Bitvector32Term::UInt64Constant(0),
                    )) == Some(true)
                {
                    return Ok(CValue::typed_pointer(Pointer::null(), target_type));
                }
                // Numeric tag equations recover coordinates and source object class,
                // never the original designation or bounds.
                return match super::pointer_tags::cast_tagged_address_to_pointer(
                    &term, assumptions, obligations, target_type,
                ) {
                    Ok(Some(pointer)) if pointer.pointer() == &Pointer::null() => Ok(CValue::Pointer(pointer)),
                    Ok(Some(pointer)) => {
                        let origin = integer_pointer_origin.ok_or_else(|| CRuntimeError::PointerConversion(
                            "integer-to-pointer cast requires a complete representation or a fresh cast identity".into(),
                        ))?;
                        Ok(CValue::Pointer(CPointerValue::new(origin, target_type)
                            .with_address(pointer.pointer().clone())
                            .with_declared_object_class(pointer.object_class())))
                    }
                    Ok(None) => Err(CRuntimeError::PointerConversion(
                        "integer-to-pointer cast requires an unchanged pointer representation, a recorded address, or zero".to_string(),
                    )),
                    Err(message) => Err(CRuntimeError::PointerConversion(message)),
                };
            }
            value => {
                return coerce_c_value_to_type_as(
                    value,
                    target_type,
                    conversion,
                    obligations,
                    assumptions,
                )
                .ok_or(CRuntimeError::TypeMismatch);
            }
        }
    }
    if let CValue::Pointer(pointer) = &value {
        if pointer.local_reference().is_some() {
            return Err(CRuntimeError::LoanRefusal(Box::new(
                crate::kernel::loans::LoanRefusal::UnsupportedResource
                    .diagnostic(crate::kernel::LoanRefusalOperation::MemoryAccess),
            )));
        }
        // Pointer-to-integer conversion under LP64: the integer is the
        // pointer's address term, which keeps the exact source pointer. Null
        // is the integer zero; function addresses are not modeled.
        if !matches!(target_type, CType::UInt64 | CType::Int64) {
            return Err(CRuntimeError::PointerConversion(
                "pointer-to-integer cast requires a 64-bit integer type under the LP64 \
                 profile; a narrower integer cannot hold a pointer"
                    .to_string(),
            ));
        }
        if pointer.block.is_function() || matches!(pointer.c_type(), CType::FunctionPointer(_)) {
            return Err(CRuntimeError::PointerConversion(
                "function addresses do not convert to integers".to_string(),
            ));
        }
        let address = Bitvector32Term::object_pointer_address(
            pointer.pointer().clone(),
            pointer.object_class(),
        );
        let numeric = match target_type {
            CType::UInt64 => CValue::UInt64(address),
            _ => CValue::Int64(address),
        };
        return Ok(CValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(numeric),
            pointer: Box::new(pointer.clone()),
            kind: PointerIntegerKind::Exact,
        }));
    }
    coerce_c_value_to_type_as(value, target_type, conversion, obligations, assumptions)
        .ok_or(CRuntimeError::TypeMismatch)
}

/// The undefined behavior of operating on `value` when it is a pointer into
/// an allocation the current snapshot has freed.
///
/// C11 6.2.4p2 makes a pointer's value indeterminate when its pointee's
/// lifetime ends, and Annex J.2 lists using such a value as undefined. Reading
/// the pointer out of a cell, storing it, or passing or returning it as a
/// pointer is not such a use in Click's model; comparing it (with anything,
/// null included), subtracting or offsetting it, testing its truth, or
/// converting it to an integer or `_Bool` (by a cast, or implicitly at an
/// assignment, a `return`, or a call argument) is. The evidence is positive: the pointer's own block holds an
/// exact deallocated base or an offset into one (see
/// [`CMemory::deallocated_heap_allocation_holding`]). A pointer whose block
/// is neither shown freed nor shown live keeps its ordinary meaning.
pub(in crate::kernel) fn freed_pointer_use(
    state: &CState,
    value: &CValue,
    assumptions: &PureFactContext,
) -> Option<CUndefinedBehavior> {
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    if pointer.is_null() || pointer.block.is_function() {
        return None;
    }
    state
        .memory()
        .deallocated_heap_allocation_holding(pointer.pointer(), assumptions)?;
    Some(CUndefinedBehavior::FreedPointerUse)
}

/// Refuses each value path whose value is a pointer into a freed allocation;
/// see [`freed_pointer_use`]. Every other path is kept as it is.
pub(in crate::kernel) fn refuse_freed_pointer_value_paths(
    state: &CState,
    paths: Vec<CExpressionPath>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if state.memory().heap_has_no_deallocations() {
        return paths;
    }
    paths
        .into_iter()
        .map(|path| match &path.outcome {
            CExpressionOutcome::Value(value) => {
                match freed_pointer_use(state, value, assumptions) {
                    Some(undefined_behavior) => CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        ..path
                    },
                    None => path,
                }
            }
            _ => path,
        })
        .collect()
}

/// Evaluates a controlling expression whose value will be tested for truth
/// (`if`, loops, `?:`, `!`, `&&`, `||`, `assert`). Testing a freed pointer's
/// truth compares it with null, so such a value is refused here; see
/// [`freed_pointer_use`].
pub(in crate::kernel) fn evaluate_c_condition_paths(
    state: &CState,
    condition: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let paths = evaluate_c_expression_paths(state, condition, assumptions, budget)?;
    Ok(refuse_freed_pointer_value_paths(state, paths, assumptions))
}

pub(in crate::kernel) fn coerce_c_null_pointer_constant(
    value: CValue,
    target_type: CType,
) -> Option<CValue> {
    if target_type.accepts(&value) {
        return Some(match value {
            CValue::Pointer(pointer) => CValue::Pointer(pointer.with_type(target_type)),
            value => value,
        });
    }
    match (target_type, value) {
        (target_type, CValue::Int32(Bitvector32Term::Constant(0))) if target_type.is_pointer() => {
            Some(CValue::typed_pointer(Pointer::null(), target_type))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn evaluate_c_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    budget.consume_expression_step()?;
    let mut paths = match expression {
        CExpression::Value(CValue::Void) => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        CExpression::Value(value) => {
            // A value the kernel substituted into an expression is introduced
            // to it here, as a read introduces a stored one.
            let mut facts = ExecutionFacts::new();
            add_narrow_integer_range_execution_pure_facts(&mut facts, assumptions, value);
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(match value {
                    CValue::Pointer(pointer) => {
                        CValue::Pointer(assumptions.pointer_value_at_entry(pointer))
                    }
                    _ => value.clone(),
                }),
                facts,
                obligations: Vec::new(),
            }]
        }
        CExpression::Variable(name)
            if state.locals.is_array_object(name) || state.locals.is_aggregate_object(name) =>
        {
            let pointer = state
                .locals
                .slot(name)
                .expect("array binding must carry a stack slot")
                .clone();
            let pointee_constant = match state.locals.binding(name) {
                Some(CLocalBinding::ArrayObject { constant, .. })
                | Some(CLocalBinding::AggregateObject { constant, .. }) => *constant,
                _ => false,
            };
            vec![CExpressionPath {
                outcome: if state.memory.has_block(&pointer.block) {
                    CExpressionOutcome::Value(CValue::typed_pointer_with_pointee_constant(
                        pointer,
                        if state.locals.is_aggregate_object(name) {
                            CType::UInt8Pointer
                        } else {
                            state
                                .locals
                                .object_type(name)
                                .and_then(CType::pointer_to)
                                .unwrap_or(CType::Int32Pointer)
                        },
                        pointee_constant,
                    ))
                } else {
                    CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone()))
                },
                facts: Vec::new().into(),
                obligations: Vec::new(),
            }]
        }
        CExpression::Variable(_) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
        CExpression::FunctionAddress(name) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::typed_pointer(
                Pointer::function(name.clone()),
                CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
            )),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        CExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct: _,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => evaluate_c_cast_paths(
            state,
            expression,
            *target_type,
            *integer_mode,
            *pointee_volatile,
            *pointee_constant,
            *explicit_qualification,
            assumptions,
            budget,
        )?,
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => evaluate_c_conditional_paths(
            state,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        )?,
        CExpression::FloatNegate(expression) => {
            evaluate_c_float_negate_paths(state, expression, assumptions, budget)?
        }
        CExpression::FloatClassification {
            expression,
            classification,
        } => evaluate_c_float_classification_paths(
            state,
            expression,
            *classification,
            assumptions,
            budget,
        )?,
        CExpression::AddressOf(target) => {
            address_of_lvalue_paths(state, target, assumptions, budget)?
        }
        CExpression::CheckedObjectAddress(target) => {
            let width = c_expression_lvalue_type(state, target)
                .map(|ty| ty.byte_width())
                .filter(|width| *width > 0);
            let mut paths = address_of_lvalue_paths(state, target, assumptions, budget)?;
            for path in &mut paths {
                if let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &path.outcome {
                    let Some(width) = width else {
                        path.outcome =
                            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch);
                        continue;
                    };
                    let outside_known_block = match (
                        pointer.pointer().offset.as_const(),
                        state
                            .memory()
                            .block_size(&pointer.pointer().block)
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
                    if pointer.pointer().is_in_null_block()
                        || outside_known_block
                        || state.memory().is_ended_local_address(pointer.pointer())
                        || state
                            .memory()
                            .is_deallocated_heap_address(pointer.pointer(), assumptions)
                    {
                        path.outcome = CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::InvalidMemory,
                        );
                        continue;
                    }
                    // A wide range states no loadable fact, which counts
                    // bytes in 32 bits. A held range that permits reading
                    // the whole referent is the same evidence of live
                    // storage, and is what a load of it would rest on.
                    if !assumptions.proves_memory_loadable(
                        state.memory(),
                        pointer.pointer(),
                        &Bitvector32Term::Constant(width),
                    ) && state.resources().permits_memory_read(
                        pointer.pointer(),
                        width,
                        assumptions,
                    ) {
                        continue;
                    }
                    let _ = add_proof_obligation_with_context(
                        &mut path.obligations,
                        assumptions,
                        Proposition::CMemoryLoadable {
                            memory: state.memory().clone(),
                            base: pointer.pointer().clone(),
                            bytes: Bitvector32Term::Constant(width),
                            wide: false,
                        },
                        Some("reference binding requires live storage for the complete referent"),
                    );
                }
            }
            paths
        }
        CExpression::Subobject { pointer, width } => {
            evaluate_c_expression_paths(state, pointer, assumptions, budget)?
                .into_iter()
                .flat_map(|path| match path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => subobject_paths(
                        pointer,
                        *width,
                        path.facts,
                        path.obligations,
                        assumptions,
                        state.resources(),
                    ),
                    CExpressionOutcome::Value(_) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    outcome => vec![CExpressionPath {
                        outcome,
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                })
                .collect()
        }
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            evaluate_c_expression_paths(state, pointer, assumptions, budget)?
                .into_iter()
                .flat_map(|path| match path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => {
                        pointer_offset_by_bytes_paths(
                            state,
                            pointer,
                            *bytes,
                            path.facts,
                            path.obligations,
                            assumptions,
                        )
                    }
                    CExpressionOutcome::Value(_) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    CExpressionOutcome::UndefinedBehavior(error) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    CExpressionOutcome::RuntimeError(error) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                })
                .collect()
        }
        CExpression::LessThan(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::LessThan,
        )?,
        CExpression::LessEqual(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::LessEqual,
        )?,
        CExpression::GreaterThan(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::GreaterThan,
        )?,
        CExpression::GreaterEqual(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::GreaterEqual,
        )?,
        CExpression::Equal(left, right) => {
            evaluate_c_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::NotEqual(left, right) => {
            evaluate_c_not_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Not(expression) => {
            evaluate_c_not_paths(state, expression, assumptions, budget)?
        }
        CExpression::And(left, right) => {
            evaluate_c_logical_and_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Or(left, right) => {
            evaluate_c_logical_or_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Add(left, right) => {
            evaluate_c_add_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Subtract(left, right) => {
            evaluate_c_subtract_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Multiply(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Divide(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Remainder(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftLeft(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftRight(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::BitwiseAnd(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::And,
                )
            },
        )?,
        CExpression::BitwiseOr(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Or,
                )
            },
        )?,
        CExpression::BitwiseXor(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Xor,
                )
            },
        )?,
        CExpression::BitwiseNot(expression) => {
            let mut paths = Vec::new();
            for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
                match path.outcome {
                    CExpressionOutcome::Value(value) => {
                        paths.extend(apply_c_bitwise_not(value, path.facts, path.obligations))
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                            facts: path.facts,
                            obligations: path.obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }),
                }
            }
            paths
        }
        // An inline array field is an lvalue whose value is not represented by
        // CValue. In an expression context it undergoes C's array-to-pointer
        // conversion, so evaluate the field's address rather than attempting
        // to load an aggregate value.
        CExpression::TypedLoad {
            pointer,
            value_type:
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int128Array(_)
                | CType::Int64Array(_)
                | CType::UInt128Array(_)
                | CType::UInt64Array(_)
                | CType::PointerArray(_, _),
            ..
        } => evaluate_c_expression_paths(state, pointer, assumptions, budget)?,
        CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
    };
    // A wide wrapper cannot reinterpret a legacy word or arithmetic node.
    // Inspect the root only, including values read from locals or call results.
    for path in &mut paths {
        if let CExpressionOutcome::Value(value @ (CValue::Int128(_) | CValue::UInt128(_))) =
            &path.outcome
            && !value.c_type().accepts(value)
        {
            path.outcome = CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch);
        }
    }
    budget.check_path_width(paths.len())?;
    for path in &paths {
        if let CExpressionOutcome::Value(value) = &path.outcome {
            crate::kernel::debug_assert_widths(
                "an evaluated expression",
                || crate::kernel::value_mismatch(value),
                value,
            );
        }
    }
    Ok(paths)
}

#[allow(clippy::too_many_arguments)] // Cast mode and pointee qualifiers are independent.
fn evaluate_c_cast_paths(
    state: &CState,
    expression: &CExpression,
    target_type: CType,
    integer_mode: CIntegerCastMode,
    pointee_volatile: bool,
    pointee_constant: bool,
    explicit_qualification: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let _word_representation = target_type
        .is_pointer()
        .then(|| WordRepresentationScope::enter(true));
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            mut facts,
            mut obligations,
        } = path;
        // Converting a freed pointer to an integer (or to `_Bool`) uses its
        // indeterminate value; a pointer-to-pointer cast only retags it, like
        // a store. See `freed_pointer_use`.
        let outcome = match outcome {
            CExpressionOutcome::Value(value) if !target_type.is_pointer() => {
                match freed_pointer_use(state, &value, assumptions) {
                    Some(undefined_behavior) => {
                        CExpressionOutcome::UndefinedBehavior(undefined_behavior)
                    }
                    None => CExpressionOutcome::Value(value),
                }
            }
            outcome => outcome,
        };
        let outcome = match outcome {
            CExpressionOutcome::Value(value) => {
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                // A cast C source or a specification wrote converts modulo
                // 2^N; any other `Standard` cast owes the range.
                let conversion = if integer_mode == CIntegerCastMode::CConversion {
                    IntegerConversion::Modular
                } else {
                    IntegerConversion::Checked
                };
                let needs_integer_origin = match &value {
                    CValue::Int64(bits) | CValue::UInt64(bits) if target_type.is_pointer() => {
                        bits.uint64_as_const() != Some(0)
                            && effective_assumptions.decide(&ConditionTerm::uint64_equal(
                                bits.clone(),
                                Bitvector32Term::UInt64Constant(0),
                            )) != Some(true)
                    }
                    _ => false,
                };
                let integer_pointer_origin = if needs_integer_origin {
                    Some(Pointer::symbolic(budget.allocate_kernel_variable()?))
                } else {
                    None
                };
                let word_bits = match &value {
                    CValue::PointerInteger(record)
                        if target_type.is_pointer()
                            && matches!(record.kind, PointerIntegerKind::Word { .. })
                            && !SPECIFICATION_READS.with(|depth| depth.get() > 0) =>
                    {
                        crate::kernel::spec::c_value_bitvector_term(&record.numeric)
                    }
                    _ => None,
                };
                let implicit_pointer_conversion = integer_mode == CIntegerCastMode::CConversion
                    && !explicit_qualification
                    && target_type.is_pointer()
                    && matches!(&value, CValue::Pointer(_));
                let coerced = if integer_mode == CIntegerCastMode::PointerCoercion
                    || implicit_pointer_conversion
                {
                    match value {
                        CValue::Pointer(pointer)
                            if target_type.is_pointer()
                                && (integer_mode != CIntegerCastMode::PointerCoercion
                                    || target_type != CType::VoidPointer
                                    || pointer.c_type().is_object_pointer()) =>
                        {
                            Ok(CValue::Pointer(pointer.with_type(target_type)))
                        }
                        _ => Err(CRuntimeError::TypeMismatch),
                    }
                } else if integer_mode == CIntegerCastMode::Modulo {
                    MachineIntegerType::from_c_type(target_type)
                        .and_then(|destination| destination.convert_modulo_value(value))
                        .ok_or(CRuntimeError::TypeMismatch)
                } else if integer_mode == CIntegerCastMode::UInt64BitsToInt64 {
                    match (target_type, value.numeric_value().clone()) {
                        (CType::Int64, CValue::UInt64(bits)) => {
                            Ok(CValue::Int64(Bitvector32Term::int64_from_uint64_bits(bits)))
                        }
                        _ => Err(CRuntimeError::TypeMismatch),
                    }
                } else if target_type == CType::Int32 {
                    match value {
                        value @ (CValue::Int8(_)
                        | CValue::Int16(_)
                        | CValue::UInt8(_)
                        | CValue::UInt16(_)) => promote_c_int32_path_value(value)
                            .map(CValue::Int32)
                            .ok_or(CRuntimeError::TypeMismatch),
                        value => cast_c_value_to_type_with_integer_origin(
                            value,
                            target_type,
                            conversion,
                            &mut obligations,
                            &effective_assumptions,
                            integer_pointer_origin,
                        ),
                    }
                } else if target_type == CType::UInt32
                    && matches!(
                        value,
                        CValue::Int8(_) | CValue::Int16(_) | CValue::UInt8(_) | CValue::UInt16(_)
                    )
                {
                    // A narrow value's range was filed where the value was
                    // produced, in both orders for an unsigned type, so the
                    // widened word needs no fact of its own.
                    promote_c_uint32_path_value(value)
                        .map(CValue::UInt32)
                        .ok_or(CRuntimeError::TypeMismatch)
                } else {
                    cast_c_value_to_type_with_integer_origin(
                        value,
                        target_type,
                        conversion,
                        &mut obligations,
                        &effective_assumptions,
                        integer_pointer_origin,
                    )
                };
                let coerced = coerced.and_then(|value| {
                    let (Some(bits), CValue::Pointer(pointer)) = (&word_bits, &value) else {
                        return Ok(value);
                    };
                    if effective_assumptions.decide(&ConditionTerm::uint64_equal(
                        bits.clone(),
                        Bitvector32Term::UInt64Constant(0),
                    )) == Some(true)
                    {
                        return Ok(CValue::typed_pointer(Pointer::null(), target_type));
                    }
                    // Only full-value premises supply the selected extent.
                    // Numeric tag equations may then choose address coordinates.
                    let pointer = effective_assumptions.pointer_value_at_entry(pointer);
                    let address = super::pointer_tags::cast_tagged_address_to_pointer(
                        bits,
                        &effective_assumptions,
                        &mut obligations,
                        target_type,
                    )
                    .map_err(CRuntimeError::PointerConversion)?;
                    Ok(CValue::Pointer(match address {
                        Some(address) => {
                            let class = pointer.object_class().or_else(|| address.object_class());
                            pointer
                                .with_address(address.pointer().clone())
                                .with_declared_object_class(class)
                        }
                        None => pointer,
                    }))
                });
                // A C conversion into a narrow type lands in that type's
                // range whatever its operand; file the range where the value
                // is produced, as a narrow read does.
                if let Ok(value) = &coerced
                    && integer_mode == CIntegerCastMode::CConversion
                    && matches!(
                        crate::kernel::c_narrow_integer_range(value),
                        Some((Bitvector32Term::MachineIntegerCast { .. }, _, _))
                    )
                {
                    add_narrow_integer_range_execution_pure_facts(&mut facts, assumptions, value);
                }
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
                                    CValue::Pointer(pointer) if pointer.pointee_constant()
                                ));
                        let pointee_volatile = pointee_volatile
                            || (integer_mode == CIntegerCastMode::PointerCoercion
                                && matches!(
                                    &value,
                                    CValue::Pointer(pointer) if pointer.pointee_volatile()
                                ));
                        CExpressionOutcome::Value(
                            value
                                .with_pointer_pointee_volatile(pointee_volatile)
                                .with_pointer_pointee_constant(pointee_constant),
                        )
                    }
                    Err(error) => CExpressionOutcome::RuntimeError(error),
                }
            }
            CExpressionOutcome::UndefinedBehavior(error) => {
                CExpressionOutcome::UndefinedBehavior(error)
            }
            CExpressionOutcome::RuntimeError(error) => CExpressionOutcome::RuntimeError(error),
        };
        paths.push(CExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_float_classification_paths(
    state: &CState,
    expression: &CExpression,
    classification: CFloatClassification,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(CValue::Float32(value)) => {
                paths.extend(condition_as_c_int32_paths(
                    ConditionTerm::float32_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            CExpressionOutcome::Value(CValue::Float64(value)) => {
                paths.extend(condition_as_c_int32_paths(
                    ConditionTerm::float64_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            CExpressionOutcome::Value(_) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts: path.facts,
                obligations: path.obligations,
            }),
            CExpressionOutcome::UndefinedBehavior(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_float_negate_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = path;
        let outcome = match outcome {
            CExpressionOutcome::Value(CValue::Float32(value)) => {
                CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::float32_negate(value)))
            }
            CExpressionOutcome::Value(CValue::Float64(value)) => {
                CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::float64_negate(value)))
            }
            CExpressionOutcome::Value(_) => {
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            }
            CExpressionOutcome::UndefinedBehavior(error) => {
                CExpressionOutcome::UndefinedBehavior(error)
            }
            CExpressionOutcome::RuntimeError(error) => CExpressionOutcome::RuntimeError(error),
        };
        paths.push(CExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_conditional_paths(
    state: &CState,
    condition: &CExpression,
    then_branch: &CExpression,
    else_branch: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_c_condition_paths(state, condition, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let CExpressionOutcome::Value(value) = outcome else {
            paths.push(CExpressionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };

        for truthiness in c_truthiness_paths(value, facts, obligations, assumptions) {
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
                evaluate_c_expression_paths(state, branch, &branch_assumptions, budget)?
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
                paths.push(CExpressionPath {
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

pub(in crate::kernel) fn evaluate_c_lvalue_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CLValuePath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Variable(name) => vec![CLValuePath {
            outcome: match state.locals.binding(name) {
                Some(CLocalBinding::Object {
                    c_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                })
                | Some(CLocalBinding::UninitializedObject {
                    c_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                }) => {
                    let lvalue = CLValue::local_with_qualifiers(
                        name.clone(),
                        *c_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant);
                    CLValueOutcome::LValue(lvalue)
                }
                Some(CLocalBinding::GlobalObject {
                    c_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                }) => CLValueOutcome::LValue(
                    CLValue::memory_with_qualifiers(
                        slot.clone(),
                        *c_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant),
                ),
                Some(CLocalBinding::ArrayObject { .. }) => {
                    CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
                // A struct object is an lvalue whose address is the object's
                // slot; its value type is the byte array holding it.
                Some(CLocalBinding::AggregateObject { layout, .. }) => CLValueOutcome::LValue(
                    CLValue::local(name.clone(), CType::UInt8Array(layout.size_bytes())),
                ),
                None => CLValueOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
        CExpression::Load(pointer_expression) => {
            let Some(value_type) = c_expression_pointee_type(state, pointer_expression) else {
                return Ok(vec![CLValuePath {
                    outcome: CLValueOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_local_reference(pointer.local_reference().copied())
                            .with_extent_of(&pointer)
                            .with_access_class(CAccessClass::of_kernel_type(value_type)),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        CExpression::TypedLoad {
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
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                *value_type,
                                *volatile || pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_local_reference(pointer.local_reference().copied())
                            .with_pointee_constant(*pointee_constant)
                            .with_extent_of(&pointer)
                            .with_access_class(access_class.clone()),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        CExpression::Index(base, index) => {
            let Some(value_type) = c_expression_pointee_type(state, base) else {
                return Ok(vec![CLValuePath {
                    outcome: CLValueOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in evaluate_c_add_paths(state, base, index, assumptions, budget)? {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_constant(pointer.pointee_constant())
                            .with_local_reference(pointer.local_reference().copied())
                            .with_extent_of(&pointer)
                            .with_access_class(CAccessClass::of_kernel_type(value_type)),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        _ => vec![CLValuePath {
            outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new().into(),
            obligations: Vec::new(),
        }],
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn read_c_lvalue_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let source = match expression {
        CExpression::TypedLoad { source, .. } => source.as_ref(),
        _ => None,
    };
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, expression, assumptions, budget)? {
        paths.extend(read_c_lvalue_paths(
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
/// through this read or as a substituted `CExpression::Value`, so the range
/// is filed at those two points, once where the value is produced, and no
/// operator that later widens the value restates it. A range the context
/// already holds exactly is not refiled.
pub(in crate::kernel) fn read_c_lvalue_paths(
    state: &CState,
    outcome: CLValueOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    source: Option<&LoadSourceId>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut access_state = None;
    if let CLValueOutcome::LValue(lvalue) = &outcome {
        if let Some(reference) = &lvalue.local_reference {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let result = lvalue
                .pointer(state)
                .ok_or(crate::kernel::loans::LoanRefusal::InvalidEvidence)
                .and_then(|pointer| {
                    state.local_scalar_access_resources(
                        reference,
                        &pointer,
                        lvalue.value_type,
                        &effective_assumptions,
                    )
                });
            match result {
                Ok((resources, _)) => {
                    access_state = Some(state.clone().with_resource_context(resources))
                }
                Err(error) => {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::LoanRefusal(
                            Box::new(
                                error.diagnostic(crate::kernel::LoanRefusalOperation::MemoryAccess),
                            ),
                        )),
                        facts,
                        obligations,
                    }]);
                }
            }
        } else if state.has_local_scalar_references() {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let pointer = match &lvalue.storage {
                CLValueStorage::Memory { pointer } => Some(pointer),
                CLValueStorage::Local { name } => state
                    .locals
                    .slot(name)
                    .filter(|pointer| state.memory.requires_explicit_scalar_ownership(pointer)),
            };
            if let Some(pointer) = pointer
                && state
                    .resources()
                    .memory_write_range(
                        pointer,
                        lvalue.value_type.byte_width(),
                        &effective_assumptions,
                    )
                    .is_none()
            {
                return Ok(vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: Box::new(CResourceFact::own_memory(
                            CMemoryRange::new_with_element_width(
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
        }
    }
    let mut paths = read_c_lvalue_paths_without_ranges(
        access_state.as_ref().unwrap_or(state),
        outcome,
        facts,
        obligations,
        source,
        assumptions,
        budget,
    )?;
    for path in &mut paths {
        let CExpressionOutcome::Value(value) = &path.outcome else {
            continue;
        };
        add_narrow_integer_range_execution_pure_facts(&mut path.facts, assumptions, value);
    }
    Ok(paths)
}

fn read_c_lvalue_paths_without_ranges(
    state: &CState,
    outcome: CLValueOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    source: Option<&LoadSourceId>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    Ok(match outcome {
        CLValueOutcome::LValue(lvalue) => match &lvalue.storage {
            CLValueStorage::Local { name } => {
                if let Some(pointer) = state.locals.slot(name)
                    && let Some(refusal) = subobject_access_refusal(
                        pointer,
                        lvalue.extent(),
                        lvalue.value_type.byte_width(),
                        &facts,
                        &obligations,
                        assumptions,
                    )
                {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    }]);
                }
                let local_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                if let Some(pointer) = state.locals.slot(name)
                    && lvalue.designation.as_deref().is_some_and(|origin| {
                        !local_assumptions.designations_equal(origin, &pointer.object_identity())
                            || !lvalue.extent_known && lvalue.opaque_extent.is_some()
                    })
                    && !state.resources().permits_designated_memory_read(
                        pointer,
                        lvalue.access_designation(),
                        lvalue.value_type.byte_width(),
                        &local_assumptions,
                    )
                {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource {
                            resource: Box::new(CResourceFact::view_memory(
                                CMemoryRange::new_with_element_width(
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
                        CLocalBinding::Object {
                            storage_declared: true,
                            ..
                        } | CLocalBinding::UninitializedObject { .. }
                    )
                ) && let Some(pointer) = state.locals.slot(name)
                    && state.memory.requires_explicit_scalar_ownership(pointer)
                    && !assumptions.should_allow_symbolic_contract_loads()
                    && !resource_context_has_read(
                        state.resources(),
                        pointer,
                        lvalue.value_type.byte_width(),
                        assumptions,
                    )
                {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource {
                            resource: Box::new(CResourceFact::view_memory(
                                CMemoryRange::new_with_element_width(
                                    pointer.clone(),
                                    0.into(),
                                    1.into(),
                                    lvalue.value_type.byte_width(),
                                ),
                            )),
                        }),
                        facts,
                        obligations,
                    }]);
                }
                let outcome = match state.locals.get(name) {
                    Some(value) if lvalue.value_type.accepts(value) => CExpressionOutcome::Value(
                        match value {
                            CValue::Pointer(pointer) => {
                                CValue::Pointer(local_assumptions.pointer_value_at_entry(pointer))
                            }
                            _ => value.clone(),
                        }
                        .with_pointer_pointee_volatile(lvalue.pointee_is_volatile())
                        .with_pointer_pointee_constant(lvalue.pointee_is_constant()),
                    ),
                    Some(_) => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    None if matches!(
                        state.locals.binding(name),
                        Some(CLocalBinding::UninitializedObject { .. })
                    ) =>
                    {
                        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                    }
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        name.clone(),
                    )),
                };
                let mut facts = facts;
                if lvalue.is_volatile()
                    && let CExpressionOutcome::Value(value) = &outcome
                    && let Some(pointer) = lvalue.pointer(state)
                {
                    facts.push(volatile_access_fact(
                        budget,
                        false,
                        pointer,
                        lvalue.value_type,
                        value.clone(),
                    )?);
                }
                vec![CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                }]
            }
            CLValueStorage::Memory { pointer } => {
                if state
                    .memory
                    .heap
                    .pending_reallocations
                    .values()
                    .any(|pending| pending.old_pointer.block == pointer.block)
                {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(
                            CRuntimeError::UnresolvedAllocationOutcome,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                if state.memory.is_ended_local_address(pointer) {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::InvalidMemory,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                if state
                    .memory
                    .is_deallocated_heap_address(pointer, assumptions)
                {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::InvalidMemory,
                        ),
                        facts,
                        obligations,
                    }]);
                }
                if let Some(refusal) = subobject_access_refusal(
                    pointer,
                    lvalue.extent(),
                    lvalue.value_type.byte_width(),
                    &facts,
                    &obligations,
                    assumptions,
                )
                .or_else(|| {
                    (!SpecificationAccessScope::is_active())
                        .then(|| effective_type_refusal(&state.memory, pointer, &lvalue))
                        .flatten()
                }) {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    }]);
                }
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let is_external = is_external_memory_pointer(pointer)
                    || state.memory.requires_explicit_scalar_ownership(pointer)
                    || lvalue.designation.as_deref().is_some_and(|origin| {
                        !effective_assumptions
                            .designations_equal(origin, &pointer.object_identity())
                            || !lvalue.extent_known && lvalue.opaque_extent.is_some()
                    });
                let require_owned = assumptions.should_require_owned_expression_loads();
                let has_read_resource = (is_external || require_owned)
                    && ((!require_owned && assumptions.should_allow_symbolic_contract_loads())
                        || crate::kernel::api::with_extended_dag_bridging(|| {
                            state.resources().permits_designated_memory_read(
                                pointer,
                                lvalue.access_designation(),
                                lvalue.value_type.byte_width(),
                                &effective_assumptions,
                            )
                        }));
                if (is_external || require_owned) && !has_read_resource {
                    return Ok(vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource {
                            resource: Box::new(CResourceFact::view_memory(
                                CMemoryRange::new_with_element_width(
                                    pointer.clone(),
                                    Bitvector32Term::Constant(0),
                                    Bitvector32Term::Constant(1),
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
                let mut paths = evaluate_c_memory_load_paths(
                    &state.memory,
                    pointer.clone(),
                    lvalue.value_type,
                    facts,
                    obligations,
                    assumptions,
                    is_external && has_read_resource,
                    lvalue.is_volatile(),
                    source,
                    budget.c_byte_order(),
                );
                // A pointer read from memory designates an object of the
                // class its lvalue's type points to, unless it carries the
                // class of the declaration that formed it.
                if let Some(pointee) = lvalue.access_class().and_then(|class| class.pointee()) {
                    for path in &mut paths {
                        if let CExpressionOutcome::Value(value) = &mut path.outcome
                            && matches!(value, CValue::Pointer(_))
                        {
                            *value = value
                                .clone()
                                .with_pointer_declared_object_class(Some(pointee.clone()));
                        }
                    }
                }
                if let Some(source) = source.and_then(|source| source.reference_access.as_ref())
                    && source.kind == crate::kernel::ReferenceAccessKind::Read
                {
                    for path in &mut paths {
                        if matches!(path.outcome, CExpressionOutcome::Value(_)) {
                            let mut fact =
                                ExecutionPureFact::certified(Proposition::CMemoryReadDefined {
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
                                    lvalue.value_type,
                                );
                            path.facts.push(fact);
                        }
                    }
                }
                if !lvalue.is_volatile() {
                    return Ok(paths);
                }
                for path in &mut paths {
                    if let CExpressionOutcome::Value(value) = &path.outcome {
                        let value = value.clone();
                        path.facts.push(volatile_access_fact(
                            budget,
                            false,
                            pointer.clone(),
                            lvalue.value_type,
                            value,
                        )?);
                    }
                }
                paths
            }
        },
        CLValueOutcome::UndefinedBehavior(undefined_behavior) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        }],
        CLValueOutcome::RuntimeError(error) => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(error),
            facts,
            obligations,
        }],
    })
}

pub(in crate::kernel) fn address_of_lvalue_paths(
    state: &CState,
    target: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        paths.push(match lvalue_path.outcome {
            CLValueOutcome::LValue(lvalue) => match lvalue.pointer(state) {
                Some(pointer) => {
                    // A struct object is stored as its byte array; its
                    // address is a struct pointer, which the C0 front end
                    // spells with the int32-pointer placeholder. Alignment
                    // of any declared object is intrinsic to its block,
                    // recorded when the block was created.
                    let is_aggregate = match &lvalue.storage {
                        CLValueStorage::Local { name } => matches!(
                            state.locals.binding(name),
                            Some(CLocalBinding::AggregateObject { .. })
                        ),
                        CLValueStorage::Memory { .. } => false,
                    };
                    let pointer_type = if is_aggregate {
                        Some(CType::Int32Pointer)
                    } else {
                        lvalue.value_type().pointer_to()
                    };
                    match pointer_type {
                        Some(pointer_type) => {
                            let facts = lvalue_path.facts;
                            let mut address = CPointerValue::new(pointer, pointer_type)
                                .with_pointee_volatile(lvalue.is_volatile())
                                .with_pointee_constant(lvalue.is_constant())
                                .with_extent(lvalue.extent().cloned());
                            if lvalue.extent_known && lvalue.extent().is_none() {
                                address = address.with_root_extent();
                            }
                            if let Some(designation) = &lvalue.designation {
                                address = address
                                    .with_designation(designation.clone())
                                    .with_opaque_extent(lvalue.opaque_extent.clone());
                            }
                            if let Some(reference) = &lvalue.local_reference {
                                address = address.with_local_reference(*reference);
                            }
                            let value = CValue::Pointer(address);
                            CExpressionPath {
                                outcome: CExpressionOutcome::Value(value),
                                facts,
                                obligations: lvalue_path.obligations,
                            }
                        }
                        None => CExpressionPath {
                            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: lvalue_path.facts,
                            obligations: lvalue_path.obligations,
                        },
                    }
                }
                None => CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        format!("{target:?}"),
                    )),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
                },
            },
            CLValueOutcome::UndefinedBehavior(undefined_behavior) => CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
            CLValueOutcome::RuntimeError(error) => CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn is_external_memory_pointer(pointer: &Pointer) -> bool {
    !pointer.block.is_local_block()
        && !pointer.block.is_global_block()
        && !pointer.block.is_static_block()
        && !pointer.block.starts_with("string:")
        && !pointer.block.is_havoc_block()
}

pub(in crate::kernel) fn resolve_local_pointer_alias(
    state: &CState,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Pointer {
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

pub(in crate::kernel) fn c_expression_pointee_type(
    state: &CState,
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::Value(value) => value.c_type().pointee_type(),
        CExpression::Variable(name) => match state.locals.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::GlobalObject { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            Some(CLocalBinding::AggregateObject { .. }) => Some(CType::UInt8),
            None => None,
        },
        CExpression::Cast { target_type, .. } => target_type.pointee_type(),
        CExpression::AddressOf(target) | CExpression::CheckedObjectAddress(target) => {
            c_expression_lvalue_type(state, target)
        }
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::Subobject { pointer, .. } => c_expression_pointee_type(state, pointer),
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Array(_) => Some(CType::Int32),
            CType::UInt8Array(_) => Some(CType::UInt8),
            CType::Int8Array(_) => Some(CType::Int8),
            CType::Int16Array(_) => Some(CType::Int16),
            CType::UInt16Array(_) => Some(CType::UInt16),
            CType::UInt32Array(_) => Some(CType::UInt32),
            CType::Int64Array(_) => Some(CType::Int64),
            CType::Int128Array(_) => Some(CType::Int128),
            CType::UInt64Array(_) => Some(CType::UInt64),
            CType::UInt128Array(_) => Some(CType::UInt128),
            CType::PointerArray(element, _) => Some(element.pointer_type()),
            value_type => value_type.pointee_type(),
        },
        CExpression::Add(left, right) => c_expression_pointee_type(state, left)
            .or_else(|| c_expression_pointee_type(state, right)),
        CExpression::Subtract(left, _) => c_expression_pointee_type(state, left),
        // An indexed pointer expression is itself the value stored in the
        // selected cell. For `slots[0]` where `slots` is `int32**`, the
        // lvalue type is `int32*`, so its pointee type is `int32`.
        CExpression::Index(base, _) => {
            c_expression_pointee_type(state, base).and_then(CType::pointee_type)
        }
        _ => None,
    }
}

pub(in crate::kernel) fn c_expression_lvalue_type(
    state: &CState,
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => state.locals.object_type(name),
        CExpression::Load(pointer) => c_expression_pointee_type(state, pointer),
        CExpression::TypedLoad { value_type, .. } => Some(*value_type),
        CExpression::Index(base, _) => c_expression_pointee_type(state, base),
        _ => None,
    }
}

pub(in crate::kernel) fn c_expression_pointer_step_width(
    state: &CState,
    expression: &CExpression,
) -> Option<u32> {
    c_expression_pointee_type(state, expression).map(CType::byte_width)
}

/// The C `int` a condition evaluates to: `1` when it holds, `0` when it does
/// not, one path per outcome the facts leave open.
pub(in crate::kernel) fn condition_as_c_int32_paths(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    condition_as_c_int32_paths_valued(condition, facts, obligations, assumptions, false)
}

/// [`condition_as_c_int32_paths`] for the condition's negation: `0` when it
/// holds, `1` when it does not.
pub(in crate::kernel) fn condition_as_c_int32_not_paths(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    condition_as_c_int32_paths_valued(condition, facts, obligations, assumptions, true)
}

pub(in crate::kernel) fn condition_as_c_int32_paths_valued(
    condition: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    negated: bool,
) -> Vec<CExpressionPath> {
    let value = |holds: bool| int32(u32::from(holds != negated));
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(holds) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value(holds)),
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
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(value(true)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(value(false)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct CTruthinessPath {
    pub(in crate::kernel) is_true: bool,
    pub(in crate::kernel) facts: ExecutionFacts,
    pub(in crate::kernel) obligations: Vec<ProofObligation>,
}

pub(in crate::kernel) fn c_truthiness_paths(
    value: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CTruthinessPath> {
    match value.numeric_value().clone() {
        CValue::PointerInteger(_) => unreachable!("numeric projection"),
        CValue::Void => unreachable!("void truthiness must be rejected by the caller"),
        CValue::Bool(bits) => {
            let is_zero = ConditionTerm::equal(bits, Bitvector32Term::Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown bool truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown bool truthiness fact should be consistent");
                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Int8(bits) => {
            let is_zero = ConditionTerm::equal(bits, Bitvector32Term::Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits) => {
            let is_zero = ConditionTerm::equal(bits, Bitvector32Term::Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Int64(bits) => {
            let is_zero = ConditionTerm::int64_equal(bits, Bitvector32Term::Int64Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::UInt64(bits) => {
            let is_zero = ConditionTerm::uint64_equal(bits, Bitvector32Term::UInt64Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        value @ (CValue::Int128(_) | CValue::UInt128(_)) => {
            let ty = MachineIntegerType::from_c_type(value.c_type()).expect("wide integer");
            let bits = match value {
                CValue::Int128(bits) | CValue::UInt128(bits) => bits,
                _ => unreachable!(),
            };
            let integer = IntegerTerm::from_machine(ty, bits).expect("typed wide integer");
            let is_zero = ConditionTerm::integer_equal(integer, IntegerTerm::constant(0.into()));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Float32(bits) => c_float_truthiness_paths(
            ConditionTerm::float32_classification(bits, CFloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        CValue::Float64(bits) => c_float_truthiness_paths(
            ConditionTerm::float64_classification(bits, CFloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        CValue::Pointer(pointer) => {
            let is_null = pointer_is_null_condition(pointer.pointer().clone());
            match decide_with_facts(assumptions, &facts, &is_null) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
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
                        CTruthinessPath {
                            is_true: true,
                            facts: nonnull_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
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

fn c_float_truthiness_paths(
    is_zero: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CTruthinessPath> {
    match decide_with_facts(assumptions, &facts, &is_zero) {
        Some(is_zero) => vec![CTruthinessPath {
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
                CTruthinessPath {
                    is_true: true,
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CTruthinessPath {
                    is_true: false,
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn c_truthiness_as_c_int32_paths(
    value: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    c_truthiness_paths(value, facts, obligations, assumptions)
        .into_iter()
        .map(|path| CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(if path.is_true { 1 } else { 0 })),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect()
}

#[cfg(test)]
mod pointer_integer_tests {
    use super::*;

    fn cast(value: CValue, ty: CType, context: &PureFactContext) -> Result<CValue, CRuntimeError> {
        let mut obligations = Vec::new();
        let result = cast_c_value_to_type_with_integer_origin(
            value,
            ty,
            IntegerConversion::Modular,
            &mut obligations,
            context,
            Some(Pointer::symbolic(Variable(991_099))),
        );
        assert!(obligations.is_empty());
        result
    }

    #[test]
    fn numeric_pointer_observation_retains_object_class_without_subobject_authority() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let root = Pointer::symbolic(Variable(991_085));
        let source = CPointerValue::new(root.clone(), CType::Int32Pointer)
            .with_object_class(Some(class.clone()))
            .with_extent(Some(SubobjectExtent {
                start: root,
                width: 4u32.into(),
            }));
        let context = PureFactContext::new();
        let encoded = cast(CValue::Pointer(source.clone()), CType::UInt64, &context).unwrap();
        let CValue::Pointer(decoded) = cast(
            encoded.numeric_value().clone(),
            CType::Float64Pointer,
            &context,
        )
        .unwrap() else {
            panic!("pointer cast")
        };
        assert_eq!(decoded.pointer(), source.pointer());
        assert_eq!(decoded.object_class(), Some(class));
        assert!(!decoded.extent_is_known());
        assert_ne!(decoded.designation(), source.designation());
    }

    #[test]
    fn pointer_integer_round_trip_retains_the_complete_pointer() {
        let root = CPointerValue::new(Pointer::symbolic(Variable(991_001)), CType::Int32Pointer);
        let member = root.clone().with_extent(Some(SubobjectExtent {
            start: root.pointer().clone(),
            width: 4u32.into(),
        }));
        let context = PureFactContext::new();
        for ty in [CType::Int64, CType::UInt64] {
            for pointer in [
                member.clone(),
                member
                    .clone()
                    .with_address(member.pointer().offset_by_bytes(4)),
            ] {
                let word = cast(CValue::Pointer(pointer.clone()), ty, &context).unwrap();
                assert_eq!(
                    cast(word.clone(), CType::Int32Pointer, &context).unwrap(),
                    CValue::Pointer(pointer)
                );
                let CValue::Pointer(opaque) =
                    cast(word.numeric_value().clone(), CType::Int32Pointer, &context).unwrap()
                else {
                    panic!("pointer")
                };
                assert!(!opaque.extent_is_known());
                assert_ne!(opaque.designation(), member.designation());
            }
        }
    }

    #[test]
    fn equal_integer_bits_do_not_exchange_pointer_extents() {
        let root = CPointerValue::new(Pointer::symbolic(Variable(991_002)), CType::Int32Pointer);
        let member = root.clone().with_extent(Some(SubobjectExtent {
            start: root.pointer().clone(),
            width: 4u32.into(),
        }));
        let context = PureFactContext::new();
        let root_word = cast(CValue::Pointer(root.clone()), CType::UInt64, &context).unwrap();
        let member_word = cast(CValue::Pointer(member.clone()), CType::UInt64, &context).unwrap();
        assert_eq!(root_word.numeric_value(), member_word.numeric_value());
        assert_ne!(root_word, member_word);
        assert_eq!(
            cast(root_word, CType::Int32Pointer, &context).unwrap(),
            CValue::Pointer(root.clone())
        );
        assert_eq!(
            cast(member_word.clone(), CType::VoidPointer, &context).unwrap(),
            CValue::Pointer(member.with_type(CType::VoidPointer))
        );
        let variable = Bitvector32Term::Variable(Variable(991_003));
        let context = context.assume_condition(
            ConditionTerm::uint64_equal(
                variable.clone(),
                c_value_bitvector_term(&member_word).unwrap(),
            ),
            true,
        );
        let CValue::Pointer(opaque) =
            cast(CValue::UInt64(variable), CType::Int32Pointer, &context).unwrap()
        else {
            panic!("pointer")
        };
        assert!(!opaque.extent_is_known());
        assert!(!context.pointer_designations_match(&opaque, &root));
    }
}

#[cfg(test)]
mod pointer_integer_partial_write_tests {
    use super::*;

    #[test]
    fn a_partial_byte_write_discards_the_representation_even_when_bits_are_unchanged() {
        let context = PureFactContext::new();
        let word = cast_c_value_to_type(
            CValue::Pointer(CPointerValue::new(
                Pointer::symbolic(Variable(995_001)),
                CType::Int32Pointer,
            )),
            CType::UInt64,
            IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let byte = crate::kernel::eval::byte_view::integer_cell_byte(&word, 0).unwrap();
        let cell = crate::kernel::eval::byte_view::ContainingIntegerCell {
            pointer: Pointer::null(),
            value: word,
            byte: 0,
        };
        let updated =
            crate::kernel::eval::byte_view::integer_cell_with_byte(&cell, &CValue::UInt8(byte))
                .unwrap();
        assert!(matches!(updated, CValue::UInt64(_)));
    }
}

#[cfg(test)]
mod pointer_integer_cast_identity_tests {
    use super::*;

    #[test]
    fn identical_numeric_bits_cannot_copy_a_casts_established_bounds() {
        let source = CPointerValue::new(Pointer::symbolic(Variable(997_001)), CType::Int32Pointer);
        let bits = Bitvector32Term::pointer_address(source.pointer().clone());
        let context = PureFactContext::new();
        let cast = |origin| {
            cast_c_value_to_type_with_integer_origin(
                CValue::UInt64(bits.clone()),
                CType::Int32Pointer,
                IntegerConversion::Modular,
                &mut Vec::new(),
                &context,
                Some(Pointer::symbolic(Variable(origin))),
            )
            .unwrap()
        };
        let CValue::Pointer(first) = cast(997_002) else {
            panic!("pointer")
        };
        let CValue::Pointer(second) = cast(997_003) else {
            panic!("pointer")
        };
        assert_eq!(first.pointer(), second.pointer());
        let context = context.assume_condition(
            ConditionTerm::pointer_value_equal(first, source.clone()),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::from_pointer_value(&source, 0u32.into(), 1u32.into(), 4),
        ));
        assert!(!resources.permits_designated_memory_read(
            second.pointer(),
            Some(second.access_designation()),
            4,
            &context
        ));
    }
}

#[cfg(test)]
mod packed_word_contract_tests {
    use super::*;

    fn cast(value: CValue, assumptions: &PureFactContext) -> CPointerValue {
        let result = cast_c_value_to_type(
            value,
            CType::Int32Pointer,
            IntegerConversion::Modular,
            &mut Vec::new(),
            assumptions,
        )
        .unwrap();
        let CValue::Pointer(pointer) = result else {
            panic!("pointer cast")
        };
        pointer
    }

    #[test]
    fn modulo_conversion_observes_bits_and_discards_the_word_carrier() {
        let word = CValue::UInt64(Bitvector32Term::UInt64Constant(4_294_967_297))
            .complete_word(Pointer::symbolic(Variable(997_030)));
        assert_eq!(
            MachineIntegerType::UInt32.convert_modulo_value(word.clone()),
            Some(CValue::UInt32(Bitvector32Term::Constant(1)))
        );
        assert_eq!(
            MachineIntegerType::UInt64.convert_modulo_value(word),
            Some(CValue::UInt64(Bitvector32Term::UInt64Constant(
                4_294_967_297
            )))
        );
    }

    #[test]
    fn complete_word_narrowing_uses_its_numeric_equality() {
        let bits = Bitvector32Term::Variable(Variable(997_020));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(bits.clone(), Bitvector32Term::UInt64Constant(41)),
            true,
        );
        let word = CValue::UInt64(bits).complete_word(Pointer::symbolic(Variable(997_021)));
        let narrowed =
            coerce_c_value_to_type(word, CType::Int32, &mut Vec::new(), &context).unwrap();
        let term = crate::kernel::spec::c_value_bitvector_term(&narrowed).unwrap();
        assert_eq!(
            context.decide(&ConditionTerm::equal(term, Bitvector32Term::Constant(41))),
            Some(true)
        );
    }

    #[test]
    fn incoming_word_carriers_need_full_equality_and_lose_it_on_withdrawal() {
        let _session = crate::kernel::VerificationSession::enter();
        let bits = Bitvector32Term::Variable(Variable(997_001));
        let word = CValue::UInt64(bits.clone()).complete_word(Pointer::symbolic(Variable(997_002)));
        let other = CValue::UInt64(bits).complete_word(Pointer::symbolic(Variable(997_003)));
        let empty = PureFactContext::new();
        let reconstructed = cast(word, &empty);
        let unrelated = cast(other, &empty);
        assert_eq!(reconstructed.pointer(), unrelated.pointer());
        assert!(!empty.pointer_designations_match(&reconstructed, &unrelated));
        let target = CPointerValue::new(Pointer::symbolic(Variable(997_004)), CType::Int32Pointer)
            .with_extent(Some(SubobjectExtent {
                start: Pointer::symbolic(Variable(997_004)),
                width: 4u32.into(),
            }));
        let numeric = empty.assume_condition(
            ConditionTerm::pointer_equal(reconstructed.pointer().clone(), target.pointer().clone()),
            true,
        );
        assert!(!numeric.pointer_designations_match(&reconstructed, &target));
        let relation = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(
                Box::new(reconstructed.clone()),
                Box::new(target.clone()),
            ),
            true,
        );
        let full = numeric.assume_proposition(relation.clone());
        assert!(full.pointer_designations_match(&reconstructed, &target));
        assert!(!full.pointer_designations_match(&unrelated, &target));
        let withdrawn = full.without_exact_fact(&relation);
        assert!(!withdrawn.pointer_designations_match(&reconstructed, &target));
    }

    #[test]
    fn modified_incoming_word_tag_bits_must_be_cleared_before_casting() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let word = CValue::UInt64(Bitvector32Term::Variable(Variable(997_010)))
            .complete_word(Pointer::symbolic(Variable(997_011)));
        let original = cast(word.clone(), &context);
        let value_of = |paths: Vec<CExpressionPath>| {
            let [path] = paths.as_slice() else {
                panic!("one scalar result")
            };
            let CExpressionOutcome::Value(value) = &path.outcome else {
                panic!("value")
            };
            value.clone()
        };
        let tagged = value_of(super::super::operators::apply_c_bitwise_binary(
            word,
            CValue::Int32(Bitvector32Term::Constant(1)),
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            super::super::operators::CBitwiseOperation::Or,
        ));
        assert!(
            cast_c_value_to_type(
                tagged.clone(),
                CType::Int32Pointer,
                IntegerConversion::Modular,
                &mut Vec::new(),
                &context
            )
            .is_err()
        );
        let cleared = value_of(super::super::operators::apply_c_bitwise_binary(
            tagged,
            CValue::Int32(Bitvector32Term::Constant(!1)),
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            super::super::operators::CBitwiseOperation::And,
        ));
        let restored = cast(cleared, &context);
        assert!(context.pointer_designations_match(&restored, &original));
        assert!(!restored.extent_is_known());
    }
}
