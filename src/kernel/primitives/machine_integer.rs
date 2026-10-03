//! Width and numeric interpretation of fixed-width integer constants.
//!
//! These are representation values, not execution certificates. A format may
//! describe 128 bits before a frontend or symbolic runtime supports that width.
//! Checked conversions preserve the numeric value; modulo conversions are an
//! explicit, separate policy for languages that specify them.

use super::{Bitvector32Term, CValue, MachineIntegerType};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// Closed set of supported representation widths. No zero or oversized shifts
/// can be introduced through a caller-supplied numeric width.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum MachineIntegerWidth {
    Bits8,
    Bits16,
    Bits32,
    Bits64,
    Bits128,
}

impl MachineIntegerWidth {
    pub const fn bits(self) -> u32 {
        match self {
            Self::Bits8 => 8,
            Self::Bits16 => 16,
            Self::Bits32 => 32,
            Self::Bits64 => 64,
            Self::Bits128 => 128,
        }
    }
}

/// A value format, independent of source spelling, ABI alignment, and the
/// widths currently admitted by a frontend or the symbolic execution model.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MachineIntegerFormat {
    width: MachineIntegerWidth,
    signed: bool,
}

impl MachineIntegerFormat {
    pub const fn new(width: MachineIntegerWidth, signed: bool) -> Self {
        Self { width, signed }
    }

    pub const fn width(self) -> MachineIntegerWidth {
        self.width
    }

    pub const fn bits(self) -> u32 {
        self.width.bits()
    }

    pub const fn byte_width(self) -> u32 {
        self.bits() / 8
    }

    pub const fn is_signed(self) -> bool {
        self.signed
    }

    const fn mask(self) -> u128 {
        if self.bits() == 128 {
            u128::MAX
        } else {
            (1u128 << self.bits()) - 1
        }
    }

    /// Inclusive exact numeric bounds. The largest allocation is 128 bits;
    /// arithmetic work is charged before constructing either BigInt.
    pub fn bounds(self) -> (BigInt, BigInt) {
        crate::instrumentation::record_deterministic_work(self.bits() as usize * 2);
        if self.signed {
            let upper = (self.mask() >> 1) as i128;
            (BigInt::from(-upper - 1), BigInt::from(upper))
        } else {
            (BigInt::from(0), BigInt::from(self.mask()))
        }
    }
}

/// A constant with a checked format and at most that format's number of bits.
/// Fields are private so malformed payload/width pairs cannot enter a consumer.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MachineIntegerConstant {
    format: MachineIntegerFormat,
    bits: u128,
}

impl MachineIntegerConstant {
    /// Interpret an explicitly supplied representation, without truncation.
    pub fn from_bits(format: MachineIntegerFormat, bits: u128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        (bits <= format.mask()).then_some(Self { format, bits })
    }

    pub fn from_signed(format: MachineIntegerFormat, value: i128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        if !format.signed {
            return Self::from_unsigned(format, u128::try_from(value).ok()?);
        }
        let upper = (format.mask() >> 1) as i128;
        if value < -upper - 1 || value > upper {
            return None;
        }
        Some(Self {
            format,
            bits: (value as u128) & format.mask(),
        })
    }

    pub fn from_unsigned(format: MachineIntegerFormat, value: u128) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        let upper = if format.signed {
            format.mask() >> 1
        } else {
            format.mask()
        };
        (value <= upper).then_some(Self {
            format,
            bits: value,
        })
    }

    /// Checked numeric conversion from an exact Integer. Huge numerals are
    /// refused by their cached bit length, before inspecting their limbs.
    pub fn from_integer(format: MachineIntegerFormat, value: &BigInt) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        if value.bits() > u64::from(format.bits()) {
            return None;
        }
        if format.signed {
            Self::from_signed(format, value.to_i128()?)
        } else {
            Self::from_unsigned(format, value.to_u128()?)
        }
    }

    /// Decimal spelling of a numeric value; parsing never wraps or reinterprets
    /// an out-of-range literal. Work is proportional to the explicit spelling.
    pub fn parse_decimal(format: MachineIntegerFormat, value: &str) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(value.len().saturating_add(1));
        if format.signed {
            Self::from_signed(format, value.parse().ok()?)
        } else {
            Self::from_unsigned(format, value.parse().ok()?)
        }
    }

    pub const fn format(self) -> MachineIntegerFormat {
        self.format
    }

    pub const fn bits(self) -> u128 {
        self.bits
    }

    fn signed_value(self) -> i128 {
        if self.format.bits() == 128 {
            self.bits as i128
        } else {
            let shift = 128 - self.format.bits();
            ((self.bits << shift) as i128) >> shift
        }
    }

    pub fn to_i128(self) -> Option<i128> {
        if self.format.signed {
            Some(self.signed_value())
        } else {
            i128::try_from(self.bits).ok()
        }
    }

    pub fn to_u128(self) -> Option<u128> {
        if self.format.signed {
            u128::try_from(self.signed_value()).ok()
        } else {
            Some(self.bits)
        }
    }

    pub fn to_integer(self) -> BigInt {
        crate::instrumentation::record_deterministic_work(self.format.bits() as usize);
        if self.format.signed {
            BigInt::from(self.signed_value())
        } else {
            BigInt::from(self.bits)
        }
    }

    /// Preserve the numeric value, including signedness changes, or refuse.
    pub fn checked_convert(self, destination: MachineIntegerFormat) -> Option<Self> {
        if self.format.signed {
            Self::from_signed(destination, self.signed_value())
        } else {
            Self::from_unsigned(destination, self.bits)
        }
    }

    /// Explicit congruence modulo 2^destination-width. This policy implements
    /// Rust integer `as` and C++20 integral conversions; it must not silently
    /// choose the implementation-defined signed narrowing policy of C.
    pub fn convert_modulo(self, destination: MachineIntegerFormat) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let extended = if self.format.signed {
            self.signed_value() as u128
        } else {
            self.bits
        };
        Self {
            format: destination,
            bits: extended & destination.mask(),
        }
    }
}

impl MachineIntegerType {
    pub const fn format(self) -> MachineIntegerFormat {
        use MachineIntegerWidth::*;
        let (width, signed) = match self {
            Self::Int8 => (Bits8, true),
            Self::UInt8 => (Bits8, false),
            Self::Int16 => (Bits16, true),
            Self::UInt16 => (Bits16, false),
            Self::Int32 => (Bits32, true),
            Self::UInt32 => (Bits32, false),
            Self::Int64 => (Bits64, true),
            Self::UInt64 => (Bits64, false),
        };
        MachineIntegerFormat::new(width, signed)
    }

    /// Produce only the supported runtime carrier, with signed narrow values
    /// sign-extended to the legacy 32-bit term representation.
    pub(crate) fn constant_term(self, value: MachineIntegerConstant) -> Option<Bitvector32Term> {
        if value.format != self.format() {
            return None;
        }
        Some(match self {
            Self::Int8 | Self::Int16 | Self::Int32 => {
                Bitvector32Term::Constant(value.to_i128()? as u32)
            }
            Self::UInt8 | Self::UInt16 | Self::UInt32 => {
                Bitvector32Term::Constant(value.to_u128()? as u32)
            }
            Self::Int64 => Bitvector32Term::Int64Constant(value.to_i128()? as i64),
            Self::UInt64 => Bitvector32Term::UInt64Constant(value.to_u128()? as u64),
        })
    }

    pub(crate) fn constant_value(self, value: MachineIntegerConstant) -> Option<CValue> {
        let term = self.constant_term(value)?;
        Some(match self {
            Self::Int8 => CValue::Int8(term),
            Self::UInt8 => CValue::UInt8(term),
            Self::Int16 => CValue::Int16(term),
            Self::UInt16 => CValue::UInt16(term),
            Self::Int32 => CValue::Int32(term),
            Self::UInt32 => CValue::UInt32(term),
            Self::Int64 => CValue::Int64(term),
            Self::UInt64 => CValue::UInt64(term),
        })
    }

    pub(crate) fn constant_from_term(
        self,
        value: &Bitvector32Term,
    ) -> Option<MachineIntegerConstant> {
        match (self, value) {
            (Self::Int8 | Self::Int16 | Self::Int32, Bitvector32Term::Constant(value)) => {
                MachineIntegerConstant::from_signed(self.format(), i128::from(*value as i32))
            }
            (Self::UInt8 | Self::UInt16 | Self::UInt32, Bitvector32Term::Constant(value)) => {
                MachineIntegerConstant::from_unsigned(self.format(), u128::from(*value))
            }
            (Self::Int64, Bitvector32Term::Int64Constant(value)) => {
                MachineIntegerConstant::from_signed(self.format(), i128::from(*value))
            }
            (Self::UInt64, Bitvector32Term::UInt64Constant(value)) => {
                MachineIntegerConstant::from_unsigned(self.format(), u128::from(*value))
            }
            _ => None,
        }
    }

    pub(crate) fn constant_from_value(self, value: &CValue) -> Option<MachineIntegerConstant> {
        if value.c_type() != self.c_type() {
            return None;
        }
        let term = match value {
            CValue::Int8(term)
            | CValue::UInt8(term)
            | CValue::Int16(term)
            | CValue::UInt16(term)
            | CValue::Int32(term)
            | CValue::UInt32(term)
            | CValue::Int64(term)
            | CValue::UInt64(term) => term,
            _ => return None,
        };
        self.constant_from_term(term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formats() -> impl Iterator<Item = MachineIntegerFormat> {
        use MachineIntegerWidth::*;
        [Bits8, Bits16, Bits32, Bits64, Bits128]
            .into_iter()
            .flat_map(|width| [false, true].map(|signed| MachineIntegerFormat::new(width, signed)))
    }

    fn types() -> impl Iterator<Item = MachineIntegerType> {
        use MachineIntegerType::*;
        [Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64].into_iter()
    }

    #[test]
    fn machine_integer_formats_have_exact_bounds_and_literal_limits() {
        for format in formats() {
            let (lo, hi) = format.bounds();
            let power = BigInt::from(1) << (format.bits() - u32::from(format.is_signed()));
            assert_eq!(hi, &power - 1);
            assert_eq!(lo, if format.is_signed() { -power } else { 0.into() });
            assert_eq!(format.byte_width() * 8, format.bits());
            for value in [lo.clone(), hi.clone(), 0.into(), 1.into()] {
                let number = MachineIntegerConstant::from_integer(format, &value).unwrap();
                assert_eq!(number.format(), format);
                assert_eq!(number.to_integer(), value);
                assert_eq!(
                    MachineIntegerConstant::parse_decimal(format, &value.to_string()),
                    Some(number)
                );
            }
            for value in [&lo - 1, &hi + 1] {
                assert!(MachineIntegerConstant::from_integer(format, &value).is_none());
                assert!(
                    MachineIntegerConstant::parse_decimal(format, &value.to_string()).is_none()
                );
            }
            for text in ["", " 1", "1 ", "0xff", "1.0", "NaN", "++1"] {
                assert!(MachineIntegerConstant::parse_decimal(format, text).is_none());
            }
        }
    }

    #[test]
    fn machine_integer_raw_representations_preserve_sign_and_reject_oversized_payloads() {
        for format in formats() {
            let mask = format.mask();
            let all_ones = MachineIntegerConstant::from_bits(format, mask).unwrap();
            assert_eq!(all_ones.bits(), mask);
            assert_eq!(
                all_ones.to_integer(),
                if format.is_signed() {
                    (-1).into()
                } else {
                    mask.into()
                }
            );
            if format.bits() != 128 {
                assert!(MachineIntegerConstant::from_bits(format, mask + 1).is_none());
            }
        }
        let signed = MachineIntegerFormat::new(MachineIntegerWidth::Bits8, true);
        let unsigned = MachineIntegerFormat::new(MachineIntegerWidth::Bits8, false);
        for bits in 0..=255u128 {
            let signed = MachineIntegerConstant::from_bits(signed, bits).unwrap();
            let unsigned = MachineIntegerConstant::from_bits(unsigned, bits).unwrap();
            assert_eq!(signed.to_i128(), Some(i128::from(bits as u8 as i8)));
            assert_eq!(unsigned.to_u128(), Some(bits));
            assert_ne!(
                signed, unsigned,
                "format is part of identity even for equal positive values"
            );
        }
    }

    fn check_conversions(source: MachineIntegerConstant) {
        let numeric = source.to_integer();
        for destination in formats() {
            let (lo, hi) = destination.bounds();
            let checked = source.checked_convert(destination);
            let fits = lo <= numeric && numeric <= hi;
            assert_eq!(checked.is_some(), fits);
            if let Some(checked) = checked {
                assert_eq!(checked.to_integer(), numeric);
                assert_eq!(checked.format(), destination);
            }
            // Independent exact arithmetic oracle; no host shifts, sign
            // extension, or reinterpretation from the implementation.
            let modulus = BigInt::from(1) << destination.bits();
            let residue = ((&numeric % &modulus) + &modulus) % &modulus;
            let expected = if destination.is_signed() && residue >= (&modulus / 2) {
                residue - &modulus
            } else {
                residue
            };
            let converted = source.convert_modulo(destination);
            assert_eq!(converted.to_integer(), expected);
            assert_eq!(converted.format(), destination);
            if let Some(checked) = checked {
                assert_eq!(converted, checked);
            }
            assert_eq!(converted.convert_modulo(destination), converted);
        }
    }

    #[test]
    fn machine_integer_checked_and_modulo_conversions_match_independent_exact_arithmetic() {
        for source in formats() {
            let (lo, hi) = source.bounds();
            for value in [
                lo.clone(),
                &lo + 1,
                (-1).into(),
                0.into(),
                1.into(),
                &hi - 1,
                hi,
            ] {
                if let Some(value) = MachineIntegerConstant::from_integer(source, &value) {
                    check_conversions(value);
                }
            }
            if source.bits() == 8 {
                for bits in 0..=255 {
                    check_conversions(MachineIntegerConstant::from_bits(source, bits).unwrap());
                }
            }
        }
    }

    #[test]
    fn machine_integer_128_bit_widening_and_narrowing_keep_numeric_and_modulo_policies_distinct() {
        let i128_format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, true);
        let u128_format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, false);
        let i64_format = MachineIntegerType::Int64.format();
        let u64_format = MachineIntegerType::UInt64.format();
        let negative = MachineIntegerConstant::from_signed(i64_format, -1).unwrap();
        let widened = negative.checked_convert(i128_format).unwrap();
        assert_eq!(widened.to_i128(), Some(-1));
        assert_eq!(widened.bits(), u128::MAX);
        assert!(negative.checked_convert(u128_format).is_none());
        assert_eq!(
            negative.convert_modulo(u128_format).to_u128(),
            Some(u128::MAX)
        );
        let unsigned =
            MachineIntegerConstant::from_unsigned(u64_format, u128::from(u64::MAX)).unwrap();
        assert_eq!(
            unsigned.checked_convert(i128_format).unwrap().to_i128(),
            Some(i128::from(u64::MAX))
        );
        let signed_min = MachineIntegerConstant::from_signed(i128_format, i128::MIN).unwrap();
        assert_eq!(signed_min.to_i128(), Some(i128::MIN));
        assert_eq!(signed_min.to_u128(), None);
        assert!(signed_min.checked_convert(i64_format).is_none());
        assert_eq!(signed_min.convert_modulo(i64_format).to_i128(), Some(0));
        let unsigned_max = MachineIntegerConstant::from_unsigned(u128_format, u128::MAX).unwrap();
        assert_eq!(unsigned_max.to_i128(), None);
        assert!(unsigned_max.checked_convert(i128_format).is_none());
        assert_eq!(unsigned_max.convert_modulo(i128_format).to_i128(), Some(-1));
        assert_eq!(
            unsigned_max.convert_modulo(u64_format).to_u128(),
            Some(u128::from(u64::MAX))
        );
    }

    #[test]
    fn machine_integer_runtime_carriers_round_trip_and_reject_wrong_width_or_signedness() {
        for ty in types() {
            let (lo, hi) = ty.format().bounds();
            for value in [lo, hi, 0.into(), 1.into()] {
                let constant = MachineIntegerConstant::from_integer(ty.format(), &value).unwrap();
                let term = ty.constant_term(constant).unwrap();
                assert_eq!(ty.constant_from_term(&term), Some(constant));
                let runtime = ty.constant_value(constant).unwrap();
                assert_eq!(runtime.c_type(), ty.c_type());
                assert_eq!(ty.constant_from_value(&runtime), Some(constant));
                for other in types().filter(|other| *other != ty) {
                    assert!(other.constant_value(constant).is_none());
                    assert!(other.constant_term(constant).is_none());
                    assert!(other.constant_from_value(&runtime).is_none());
                }
            }
        }
        let ty = MachineIntegerType::Int8;
        // Narrow signed terms are sign-extended to 32 bits, never truncated
        // from a malformed carrier that merely shares their low bits.
        assert!(
            ty.constant_from_term(&Bitvector32Term::Constant(255))
                .is_none()
        );
        assert_eq!(
            ty.constant_from_term(&Bitvector32Term::Constant(u32::MAX))
                .unwrap()
                .to_i128(),
            Some(-1)
        );
        assert!(
            MachineIntegerType::Int64
                .constant_from_term(&Bitvector32Term::UInt64Constant(u64::MAX))
                .is_none()
        );
        for format in formats().filter(|format| format.bits() == 128) {
            let wide = MachineIntegerConstant::from_unsigned(format, 0).unwrap();
            for ty in types() {
                assert!(ty.constant_value(wide).is_none());
            }
        }
    }

    #[test]
    fn machine_integer_constant_work_is_linear_and_oversized_integer_rejection_is_constant() {
        let format = MachineIntegerFormat::new(MachineIntegerWidth::Bits128, true);
        let source =
            MachineIntegerConstant::from_signed(MachineIntegerType::Int64.format(), -1).unwrap();
        let mut previous = None;
        for size in [4, 16, 64, 256, 1024] {
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..size {
                    let widened = source.checked_convert(format).unwrap();
                    assert_eq!(widened.checked_convert(source.format()), Some(source));
                    assert_eq!(widened.convert_modulo(source.format()), source);
                }
            });
            if let Some(previous) = previous {
                assert_eq!(work, previous * 4);
            }
            assert!(work > 0);
            previous = Some(work);
        }
        let mut previous = None;
        for bits in [256usize, 1024, 4096, 16384, 65536] {
            let value = BigInt::from(1) << bits;
            let (rejected, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerConstant::from_integer(format, &value).is_none()
            });
            assert!(rejected);
            assert!(work > 0);
            if let Some(previous) = previous {
                assert_eq!(work, previous);
            }
            previous = Some(work);
        }
        let mut previous = None;
        for size in [16, 64, 256, 1024] {
            let spelling = format!("{}1", "0".repeat(size));
            let (value, work) = crate::instrumentation::measure_deterministic_work(|| {
                MachineIntegerConstant::parse_decimal(format, &spelling)
            });
            assert_eq!(value.unwrap().to_i128(), Some(1));
            assert_eq!(work, size + 3);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }
}
