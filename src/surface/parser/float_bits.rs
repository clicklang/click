//! Literal-only IEEE bit-pattern forms. No numeric conversion or proof fact
//! participates in constructing the existing float value.
use super::*;

pub(super) fn literal_token(tokens: &[Token], index: usize) -> bool {
    index >= 2
        && matches!(&tokens[index - 2], Token::Ident(name) if matches!(name.as_str(), "float32_from_bits" | "float64_from_bits"))
        && tokens[index - 1] == Token::LParen
        && tokens.get(index + 1) == Some(&Token::RParen)
}

impl Parser {
    pub(super) fn parse_float_bits(
        &mut self,
        width: u32,
    ) -> Result<ContractExpression, ClickError> {
        let name = format!("float{width}_from_bits");
        let error = || {
            format!(
                "{name} expects one nonnegative {width}-bit integer literal (unsuffixed or u{width})"
            )
        };
        self.position += 2; // The caller selected the name and opening parenthesis.
        let (bits, explicit_u32) = match self.next() {
            Some(Token::Number(value)) => (u64::from(value), false),
            Some(Token::UnsuffixedInt64(value)) => (value as u64, false),
            Some(Token::UnsuffixedUInt64(value)) => (value, false),
            Some(Token::BigNumber(value)) => (
                value.parse::<u64>().map_err(|_| self.error(error()))?,
                false,
            ),
            Some(Token::UInt32Number(value)) if width == 32 => (u64::from(value), true),
            Some(Token::UInt64Number(value)) if width == 64 => (value, false),
            Some(Token::RustInteger(literal)) => {
                use rust_literals::IntegerSuffix;
                let explicit_u32 = match literal.suffix {
                    None => false,
                    Some(IntegerSuffix::U32) if width == 32 => true,
                    Some(IntegerSuffix::U64) if width == 64 => false,
                    _ => return Err(self.error(error())),
                };
                (
                    literal
                        .digits
                        .parse::<u64>()
                        .map_err(|_| self.error(error()))?,
                    explicit_u32,
                )
            }
            _ => return Err(self.error(error())),
        };
        if width == 32 && bits > u64::from(u32::MAX) {
            return Err(self.error(error()));
        }
        if self.peek() != Some(&Token::RParen) {
            return Err(self.error(error()));
        }
        self.position += 1;
        let value = if width == 32 {
            ProgramValue::Float32(if explicit_u32 {
                MachineTerm::uint32_constant(bits as u32)
            } else {
                MachineTerm::constant(bits as u32)
            })
        } else {
            ProgramValue::Float64(MachineTerm::uint64_constant(bits))
        };
        Ok(ContractExpression::ProgramExpression(
            ProgramExpression::Value(value),
        ))
    }
}
