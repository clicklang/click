//! Constant numeric conversions shared by evaluation and term rebuilding.
use super::*;

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

pub(in crate::kernel) fn integer_to_float32_bits(negative: bool, magnitude: u128) -> u32 {
    integer_to_float_bits(negative, magnitude, 23, 8, 127, 0x8000_0000) as u32
}

pub(in crate::kernel) fn integer_to_float64_bits(negative: bool, magnitude: u128) -> u64 {
    integer_to_float_bits(negative, magnitude, 52, 11, 1023, 0x8000_0000_0000_0000)
}

pub(in crate::kernel) fn float32_to_float64_bits(bits: u32) -> u64 {
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

fn integer_constant_as_sign_magnitude(value: &ProgramValue) -> Option<(bool, u128)> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Bool(bits) => Some((false, u128::from(bits.as_const()?))),
        narrow @ (ProgramValue::Int8(_)
        | ProgramValue::UInt8(_)
        | ProgramValue::Int16(_)
        | ProgramValue::UInt16(_)) => {
            let value = MachineIntegerType::from_program_type(narrow.program_type())?
                .constant_from_value(narrow)?
                .to_i128()?;
            Some((value < 0, value.unsigned_abs()))
        }
        ProgramValue::Int32(bits) => {
            let value = bits.as_const()? as i32;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        ProgramValue::UInt32(bits) => Some((false, u128::from(bits.as_const()?))),
        ProgramValue::Int64(bits) => {
            let value = bits.int64_as_const()?;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        ProgramValue::UInt64(bits) => Some((false, u128::from(bits.uint64_as_const()?))),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_)
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_) => None,
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

fn float_to_integer_value(
    negative: bool,
    magnitude: u128,
    target_type: ProgramType,
) -> Option<ProgramValue> {
    let signed_limit = |bits: u32| (1i128 << (bits - 1)) - 1;
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
            ProgramType::Int8 => crate::kernel::int8(value as i32 as u32),
            ProgramType::Int16 => crate::kernel::int16(value as i32 as u32),
            ProgramType::Int32 => ProgramValue::Int32(MachineTerm::constant(value as i32 as u32)),
            ProgramType::Int64 => ProgramValue::Int64(MachineTerm::int64_constant(value as i64)),
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
        ProgramType::UInt8 => crate::kernel::uint8(value as u32),
        ProgramType::UInt16 => crate::kernel::uint16(value as u32),
        ProgramType::UInt32 => ProgramValue::UInt32(MachineTerm::uint32_constant(value as u32)),
        ProgramType::UInt64 => ProgramValue::UInt64(MachineTerm::uint64_constant(value)),
        _ => unreachable!(),
    })
}

pub(in crate::kernel) fn float32_to_integer_value(
    bits: u32,
    target_type: ProgramType,
) -> Option<ProgramValue> {
    let negative = bits & 0x8000_0000 != 0;
    let exponent = (bits >> 23) & 0xff;
    let fraction = u64::from(bits & 0x007f_ffff);
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 23, 8, 127)?;
    float_to_integer_value(negative, magnitude, target_type)
}

pub(in crate::kernel) fn float64_to_integer_value(
    bits: u64,
    target_type: ProgramType,
) -> Option<ProgramValue> {
    let negative = bits & (1u64 << 63) != 0;
    let exponent = ((bits >> 52) & 0x7ff) as u32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 52, 11, 1023)?;
    float_to_integer_value(negative, magnitude, target_type)
}

fn conversion_type(name: &str) -> Option<ProgramType> {
    Some(match name {
        "int8" => ProgramType::Int8,
        "uint8" => ProgramType::UInt8,
        "int16" => ProgramType::Int16,
        "uint16" => ProgramType::UInt16,
        "int32" => ProgramType::Int32,
        "uint32" => ProgramType::UInt32,
        "int64" => ProgramType::Int64,
        "uint64" => ProgramType::UInt64,
        "float32" => ProgramType::Float32,
        "float64" => ProgramType::Float64,
        _ => return None,
    })
}

/// The existing native conversion namespace, with no evaluation or allocation.
pub(crate) fn numeric_float_conversion_types(name: &str) -> Option<(ProgramType, ProgramType)> {
    if name.len() > "c_float64_to_float64".len() {
        return None;
    }
    let (source, target) = name.strip_prefix("c_")?.split_once("_to_")?;
    let source = conversion_type(source)?;
    let target = conversion_type(target)?;
    if source == target
        || !matches!(source, ProgramType::Float32 | ProgramType::Float64)
            && !matches!(target, ProgramType::Float32 | ProgramType::Float64)
    {
        return None;
    }
    Some((source, target))
}

/// Fold only a literal operand of an existing C numeric float conversion.
/// Rebuilders already visit children: do not scan a symbolic subtree here.
fn constant_conversion(name: &str, operand: &MachineTerm) -> Option<MachineTerm> {
    crate::instrumentation::record_deterministic_work(1);
    if !matches!(operand, MachineTerm::Constant { .. }) || name.len() > "c_float64_to_float64".len()
    {
        return None;
    }
    let (source, target) = numeric_float_conversion_types(name)?;
    match (source, target) {
        (ProgramType::Float32, ProgramType::Float64) => Some(MachineTerm::uint64_constant(
            float32_to_float64_bits(operand.float32_as_const()?),
        )),
        (ProgramType::Float64, ProgramType::Float32) => Some(MachineTerm::constant(
            float64_to_float32_bits(operand.float64_as_const()?),
        )),
        (source, ProgramType::Float32 | ProgramType::Float64) => {
            let format = MachineIntegerType::from_program_type(source)?;
            let value = format.value_from_term(operand.clone());
            let (negative, magnitude) = integer_constant_as_sign_magnitude(&value)?;
            Some(if target == ProgramType::Float32 {
                MachineTerm::constant(integer_to_float32_bits(negative, magnitude))
            } else {
                MachineTerm::uint64_constant(integer_to_float64_bits(negative, magnitude))
            })
        }
        (ProgramType::Float32 | ProgramType::Float64, target) => {
            let value = if source == ProgramType::Float32 {
                float32_to_integer_value(operand.float32_as_const()?, target)?
            } else {
                float64_to_integer_value(operand.float64_as_const()?, target)?
            };
            match value {
                crate::kernel::integer64_c_value!(term) => Some(term),
                _ => None,
            }
        }
        _ => None,
    }
}

impl MachineTerm {
    /// Rebuild an existing native application. Only recognized numeric float
    /// conversions with literal operands simplify; ordinary calls keep identity.
    /// Undefined float-to-integer constants stay symbolic: this operation never
    /// manufactures or discharges the evaluator's finite/range obligations.
    pub(crate) fn rebuild_pure_application(name: String, arguments: Vec<Self>) -> Self {
        if let [operand] = arguments.as_slice()
            && let Some(value) = constant_conversion(&name, operand)
        {
            return value;
        }
        Self::PureFunctionApplication { name, arguments }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conversion_rebuild_preserves_unknown_calls_and_undefined_constants() {
        for (name, arguments) in [
            ("ordinary_call", vec![MachineTerm::constant(1)]),
            ("c_int128_to_float32", vec![MachineTerm::constant(1)]),
            ("c_bool_to_float32", vec![MachineTerm::constant(1)]),
            ("c_int32_to_float32", vec![]),
            (
                "c_int32_to_float32",
                vec![MachineTerm::constant(1), MachineTerm::constant(2)],
            ),
            (
                "c_float32_to_int32",
                vec![MachineTerm::constant(0x7fc00001)],
            ),
            (
                "c_float64_to_uint64",
                vec![MachineTerm::uint64_constant(0xbff0000000000000)],
            ),
            (
                "c_float64_to_int64",
                vec![MachineTerm::uint64_constant(0x7ff0000000000000)],
            ),
        ] {
            let expected = MachineTerm::PureFunctionApplication {
                name: name.into(),
                arguments: arguments.clone(),
            };
            assert_eq!(
                MachineTerm::rebuild_pure_application(name.into(), arguments),
                expected
            );
        }
    }

    #[test]
    fn conversion_rebuild_uses_existing_exact_bits_and_truncation() {
        for (name, operand, expected) in [
            (
                "c_int32_to_float32",
                MachineTerm::constant(16_777_217),
                MachineTerm::constant(0x4b800000),
            ),
            (
                "c_float32_to_float64",
                MachineTerm::constant(0x80000000),
                MachineTerm::uint64_constant(0x8000000000000000),
            ),
            (
                "c_float32_to_float64",
                MachineTerm::constant(0x7f800123),
                MachineTerm::uint64_constant(0x7ff0002460000000),
            ),
            (
                "c_float64_to_float32",
                MachineTerm::uint64_constant(0xfff8000000000123),
                MachineTerm::constant(0xffc00000),
            ),
            (
                "c_float32_to_int32",
                MachineTerm::constant(0xbff00000),
                MachineTerm::constant(u32::MAX),
            ),
            (
                "c_float64_to_uint64",
                MachineTerm::uint64_constant(0x3ffc000000000000),
                MachineTerm::uint64_constant(1),
            ),
        ] {
            assert_eq!(
                MachineTerm::opaque_conversion(name, operand),
                expected,
                "{name}"
            );
        }
    }
}
