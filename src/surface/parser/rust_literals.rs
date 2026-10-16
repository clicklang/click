//! Integer literal spellings for Rust sidecars. Suffixes fix a native type;
//! unsuffixed magnitudes remain specification integers for contextual typing.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum IntegerSuffix {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl IntegerSuffix {
    fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "isize" => Self::Isize,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "usize" => Self::Usize,
            _ => return None,
        })
    }

    fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::Isize => "isize",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
        }
    }

    fn signed_width(self) -> (bool, u32) {
        match self {
            Self::I8 => (true, 8),
            Self::I16 => (true, 16),
            Self::I32 => (true, 32),
            Self::I64 | Self::Isize => (true, 64),
            Self::U8 => (false, 8),
            Self::U16 => (false, 16),
            Self::U32 => (false, 32),
            Self::U64 | Self::Usize => (false, 64),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct IntegerLiteral {
    pub digits: String,
    pub suffix: Option<IntegerSuffix>,
}

impl IntegerLiteral {
    pub(super) fn parse(spelling: &str) -> Result<Self, String> {
        let (radix, digits) = if let Some(digits) = spelling.strip_prefix("0x") {
            (16, digits)
        } else if let Some(digits) = spelling.strip_prefix("0o") {
            (8, digits)
        } else if let Some(digits) = spelling.strip_prefix("0b") {
            (2, digits)
        } else {
            (10, spelling)
        };
        let end = digits
            .find(|ch: char| {
                !(ch == '_'
                    || if radix == 16 {
                        ch.is_ascii_hexdigit()
                    } else {
                        ch.is_ascii_digit()
                    })
            })
            .unwrap_or(digits.len());
        let suffix = &digits[end..];
        let suffix = if suffix.is_empty() {
            None
        } else {
            Some(IntegerSuffix::parse(suffix).ok_or_else(|| {
                format!("unsupported integer literal suffix `{suffix}` in `{spelling}`")
            })?)
        };
        let digits = digits[..end].replace('_', "");
        if digits.is_empty() || !digits.chars().all(|ch| ch.is_digit(radix)) {
            return Err(format!("invalid base-{radix} integer literal `{spelling}`"));
        }
        let digits = if radix == 10 {
            let trimmed = digits.trim_start_matches('0');
            if trimmed.is_empty() {
                "0".into()
            } else {
                trimmed.into()
            }
        } else {
            // No machine-width truncation: unsuffixed literals can also denote
            // arbitrary-precision specification integers.
            num_bigint::BigUint::parse_bytes(digits.as_bytes(), radix)
                .expect("validated radix digits")
                .to_str_radix(10)
        };
        Ok(Self { digits, suffix })
    }

    pub(super) fn describe(&self) -> String {
        format!(
            "integer literal `{}{}`",
            self.digits,
            self.suffix.map_or("", IntegerSuffix::name)
        )
    }

    fn native_value(&self, negative: bool) -> Result<CValue, String> {
        let suffix = self.suffix.expect("typed literal");
        let (signed, width) = suffix.signed_width();
        if negative && !signed {
            return Err(format!(
                "cannot negate a `{}` integer literal",
                suffix.name()
            ));
        }
        let limit = if signed {
            (1u64 << (width - 1)) - u64::from(!negative)
        } else {
            u64::MAX >> (64 - width)
        };
        let value = self
            .digits
            .parse::<u64>()
            .ok()
            .filter(|value| *value <= limit)
            .ok_or_else(|| {
                format!(
                    "{}{} is out of range for `{}` (maximum magnitude {limit})",
                    if negative { "-" } else { "" },
                    self.digits,
                    suffix.name()
                )
            })?;
        let bits = if negative {
            0u64.wrapping_sub(value)
        } else {
            value
        };
        let narrow = Bitvector32Term::Constant(bits as u32);
        Ok(match suffix {
            IntegerSuffix::I8 => CValue::Int8(narrow),
            IntegerSuffix::I16 => CValue::Int16(narrow),
            IntegerSuffix::I32 => CValue::Int32(narrow),
            IntegerSuffix::U8 => CValue::UInt8(narrow),
            IntegerSuffix::U16 => CValue::UInt16(narrow),
            IntegerSuffix::U32 => CValue::UInt32(narrow),
            IntegerSuffix::I64 | IntegerSuffix::Isize => {
                CValue::Int64(Bitvector32Term::Int64Constant(bits as i64))
            }
            IntegerSuffix::U64 | IntegerSuffix::Usize => {
                CValue::UInt64(Bitvector32Term::UInt64Constant(bits))
            }
        })
    }

    pub(super) fn contract_expression(&self, negative: bool) -> Result<ContractExpression, String> {
        if self.suffix.is_some() {
            return Ok(ContractExpression::CFragment(CExpression::Value(
                self.native_value(negative)?,
            )));
        }
        let expression = ContractExpression::IntegerLiteral(self.digits.clone());
        Ok(if negative {
            ContractExpression::Negate(Box::new(expression))
        } else {
            expression
        })
    }

    pub(super) fn signed_i64(&self, negative: bool) -> Result<i64, String> {
        if self.suffix.is_some() {
            self.native_value(negative)?;
        }
        let magnitude = self
            .digits
            .parse::<u64>()
            .map_err(|_| "integer literal does not fit i64".to_string())?;
        if negative && magnitude == 1 << 63 {
            return Ok(i64::MIN);
        }
        let value =
            i64::try_from(magnitude).map_err(|_| "integer literal does not fit i64".to_string())?;
        Ok(if negative { -value } else { value })
    }

    pub(super) fn c_expression(&self, negative: bool) -> Result<C0Expression, String> {
        let value = if self.suffix.is_some() {
            self.native_value(negative)?
        } else {
            let magnitude = self
                .digits
                .parse::<u64>()
                .map_err(|_| "integer literal does not fit a native integer".to_string())?;
            if negative {
                if magnitude <= 1 << 31 {
                    CValue::Int32(Bitvector32Term::Constant(
                        0u32.wrapping_sub(magnitude as u32),
                    ))
                } else if magnitude <= 1 << 63 {
                    CValue::Int64(Bitvector32Term::Int64Constant(
                        0u64.wrapping_sub(magnitude) as i64
                    ))
                } else {
                    return Err("negative integer literal does not fit i64".into());
                }
            } else if magnitude <= i32::MAX as u64 {
                CValue::Int32(Bitvector32Term::Constant(magnitude as u32))
            } else if magnitude <= i64::MAX as u64 {
                CValue::Int64(Bitvector32Term::Int64Constant(magnitude as i64))
            } else {
                CValue::UInt64(Bitvector32Term::UInt64Constant(magnitude))
            }
        };
        Ok(match value {
            CValue::Int32(Bitvector32Term::Constant(bits)) => C0Expression::Int32Literal(bits),
            CValue::UInt8(Bitvector32Term::Constant(bits)) => {
                C0Expression::UInt8Literal(bits as u8)
            }
            CValue::UInt32(Bitvector32Term::Constant(bits)) => C0Expression::UInt32Literal(bits),
            CValue::Int64(Bitvector32Term::Int64Constant(value)) => {
                C0Expression::Int64Literal(value)
            }
            CValue::UInt64(Bitvector32Term::UInt64Constant(value)) => {
                C0Expression::UInt64Literal(value)
            }
            CValue::Int8(Bitvector32Term::Constant(bits))
            | CValue::Int16(Bitvector32Term::Constant(bits))
            | CValue::UInt16(Bitvector32Term::Constant(bits)) => C0Expression::Cast {
                c_type: match value {
                    CValue::Int8(_) => C0Type::Int8,
                    CValue::Int16(_) => C0Type::Int16,
                    _ => C0Type::UInt16,
                },
                expression: Box::new(C0Expression::Int32Literal(bits)),
                struct_name: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
            _ => unreachable!("literal constants"),
        })
    }
}

/// Normalize the old explicit suffixes too, so Rust has one range-checking
/// path regardless of whether a spelling was already supported by C sidecars.
pub(super) fn normalize_tokens(tokens: &mut [Token]) {
    for token in tokens {
        let (value, suffix) = match token {
            Token::UInt8Number(value) => (u64::from(*value), IntegerSuffix::U8),
            Token::UInt32Number(value) => (u64::from(*value), IntegerSuffix::U32),
            Token::UInt64Number(value) => (*value, IntegerSuffix::U64),
            Token::Int64Number(value) => (*value as u64, IntegerSuffix::I64),
            Token::Int64MinimumMagnitude => (1 << 63, IntegerSuffix::I64),
            _ => continue,
        };
        *token = Token::RustInteger(std::sync::Arc::new(IntegerLiteral {
            digits: value.to_string(),
            suffix: Some(suffix),
        }));
    }
}

impl Parser {
    /// Rust permits parentheses between unary minus and a minimum literal,
    /// but not an intervening operation that would first evaluate it positive.
    pub(super) fn negated_rust_literal(&self) -> Option<(std::sync::Arc<IntegerLiteral>, usize)> {
        let mut index = self.position + 1;
        let mut parentheses = 0;
        while self.tokens.get(index) == Some(&Token::LParen) {
            parentheses += 1;
            index += 1;
        }
        let Token::RustInteger(literal) = self.tokens.get(index)? else {
            return None;
        };
        index += 1;
        for _ in 0..parentheses {
            if self.tokens.get(index) != Some(&Token::RParen) {
                return None;
            }
            index += 1;
        }
        Some((literal.clone(), index))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rust_integer_literals_keep_native_fragment_and_selector_widths() {
        let parser = |expression: &str| {
            Parser::new(&format!("{expression}; verifying \"literals.rs\";")).unwrap()
        };
        assert_eq!(
            parser("-0x8000_0000i64").parse_ensure_expression().unwrap(),
            C0Expression::Int64Literal(-2147483648)
        );
        assert_eq!(
            parser("-(0x8000_0000i32)")
                .parse_ensure_expression()
                .unwrap(),
            C0Expression::Int32Literal(i32::MIN as u32)
        );
        let expression = parser("0xff_ffu16").parse_ensure_expression().unwrap();
        assert!(matches!(
            expression,
            C0Expression::Cast {
                c_type: C0Type::UInt16,
                ..
            }
        ));
        assert_eq!(parser("0x10usize").expect_number("selector").unwrap(), 16);
        assert_eq!(
            parser("-0x8000_0000_0000_0000isize")
                .expect_signed_i64("bound")
                .unwrap(),
            i64::MIN
        );
        for invalid in ["0x8000_0000i32", "-(0x8000_0000i32 + 0)", "65536u16"] {
            assert!(
                parser(invalid).parse_ensure_expression().is_err(),
                "{invalid}"
            );
        }
    }
}
