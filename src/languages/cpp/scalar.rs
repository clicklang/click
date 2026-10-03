//! Scalar interpretation for the pinned C++ target. Clang retains promotions as
//! explicit typed casts; this module does not infer C++ types from syntax.
use super::CppType;
use crate::kernel::{self, CExpression, CType};
use crate::languages::c::syntax::C0Type;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScalarKind {
    Bool,
    Int32,
    Int64,
    UInt32,
    UInt64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Scalar {
    pub kind: ScalarKind,
    pub is_const: bool,
}

impl Scalar {
    pub fn of(value: &CppType) -> Option<Self> {
        let (kind, is_const) = match value {
            CppType::Boolean { bits: 8, is_const } => (ScalarKind::Bool, *is_const),
            CppType::Integer {
                bits,
                signed,
                is_const,
                ..
            } => (
                match (*bits, *signed) {
                    (32, true) => ScalarKind::Int32,
                    (64, true) => ScalarKind::Int64,
                    (32, false) => ScalarKind::UInt32,
                    (64, false) => ScalarKind::UInt64,
                    _ => return None,
                },
                *is_const,
            ),
            _ => return None,
        };
        Some(Self { kind, is_const })
    }

    pub fn mutable_kind(value: &CppType) -> Option<ScalarKind> {
        Self::of(value)
            .filter(|scalar| !scalar.is_const)
            .map(|scalar| scalar.kind)
    }

    pub fn is(value: &CppType, kind: ScalarKind, is_const: bool) -> bool {
        Self::of(value) == Some(Self { kind, is_const })
    }
}

impl ScalarKind {
    pub fn is_integer(self) -> bool {
        self != Self::Bool
    }

    pub fn kernel_type(self) -> CType {
        match self {
            Self::Bool => CType::Bool,
            Self::Int32 => CType::Int32,
            Self::Int64 => CType::Int64,
            Self::UInt32 => CType::UInt32,
            Self::UInt64 => CType::UInt64,
        }
    }

    pub fn proof_type(self) -> C0Type {
        match self {
            Self::Bool => C0Type::Bool,
            Self::Int32 => C0Type::Int32,
            Self::Int64 => C0Type::Int64,
            Self::UInt32 => C0Type::UInt32,
            Self::UInt64 => C0Type::UInt64,
        }
    }

    pub fn parse_literal(self, value: &str) -> Option<ScalarLiteral> {
        match self {
            Self::Int32 => value.parse().ok().map(ScalarLiteral::Int32),
            Self::Int64 => value.parse().ok().map(ScalarLiteral::Int64),
            Self::UInt32 => value.parse().ok().map(ScalarLiteral::UInt32),
            Self::UInt64 => value.parse().ok().map(ScalarLiteral::UInt64),
            Self::Bool => None, // Boolean constants use the retained integral cast.
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScalarLiteral {
    Int32(i32),
    Int64(i64),
    UInt32(u32),
    UInt64(u64),
}

impl ScalarLiteral {
    pub fn kernel_expression(self) -> CExpression {
        match self {
            Self::Int32(value) => kernel::c_int32_literal(value as u32),
            Self::Int64(value) => kernel::c_int64_literal(value),
            Self::UInt32(value) => kernel::c_uint32_literal(value),
            Self::UInt64(value) => kernel::c_uint64_literal(value),
        }
    }
}

/// C++20 signed conversions are congruent modulo the destination width.
/// Shared C casts handle Boolean, unsigned, widening, and same-width int32
/// conversions. These two cases explicitly retain bits for signed results.
pub(super) fn convert(value: CExpression, source: ScalarKind, target: ScalarKind) -> CExpression {
    match (source, target) {
        (ScalarKind::UInt64, ScalarKind::Int64) => kernel::c_uint64_bits_to_int64(value),
        (ScalarKind::Int64 | ScalarKind::UInt64, ScalarKind::Int32) => {
            kernel::c_cast(kernel::c_cast(value, CType::UInt32), CType::Int32)
        }
        _ => kernel::c_cast(value, target.kernel_type()),
    }
}

pub(super) fn same_unqualified_integer_type(left: &CppType, right: &CppType) -> bool {
    matches!(
        (left, right),
        (
            CppType::Integer {
                bits: left_bits,
                signed: left_signed,
                ..
            },
            CppType::Integer {
                bits: right_bits,
                signed: right_signed,
                ..
            }
        ) if left_bits == right_bits && left_signed == right_signed
    )
}

pub(super) fn same_scalar_type(left: &CppType, right: &CppType) -> bool {
    match (left, right) {
        (
            CppType::Integer {
                bits: left_bits,
                signed: left_signed,
                is_const: left_const,
                ..
            },
            CppType::Integer {
                bits: right_bits,
                signed: right_signed,
                is_const: right_const,
                ..
            },
        ) => left_bits == right_bits && left_signed == right_signed && left_const == right_const,
        (
            CppType::Boolean {
                bits: left_bits,
                is_const: left_const,
            },
            CppType::Boolean {
                bits: right_bits,
                is_const: right_const,
            },
        ) => left_bits == right_bits && left_const == right_const,
        _ => left == right,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_classification_preserves_qualification_and_rejects_unsupported_widths() {
        for bits in [0, 1, 8, 16, 32, 64, 128] {
            for signed in [false, true] {
                for is_const in [false, true] {
                    let ty = CppType::Integer {
                        bits,
                        signed,
                        is_const,
                        source_aliases: vec![],
                    };
                    let scalar = Scalar::of(&ty);
                    assert_eq!(scalar.is_some(), matches!(bits, 32 | 64));
                    assert_eq!(
                        Scalar::mutable_kind(&ty).is_some(),
                        matches!(bits, 32 | 64) && !is_const
                    );
                    if let Some(scalar) = scalar {
                        assert_eq!(scalar.is_const, is_const);
                        // Qualifiers are preserved independently of value kind.
                        let unqualified = CppType::Integer {
                            bits,
                            signed,
                            is_const: false,
                            source_aliases: vec![],
                        };
                        assert!(same_unqualified_integer_type(&ty, &unqualified));
                        assert_eq!(same_scalar_type(&ty, &unqualified), !is_const);
                        assert!(
                            Scalar::of(&CppType::Pointer {
                                pointee: Box::new(ty)
                            })
                            .is_none()
                        );
                    }
                }
            }
        }
        for bits in [1, 8, 32] {
            assert_eq!(
                Scalar::mutable_kind(&CppType::Boolean {
                    bits,
                    is_const: false
                }),
                (bits == 8).then_some(ScalarKind::Bool)
            );
        }
    }

    #[test]
    fn integer_literals_use_one_checked_interpretation_at_both_boundaries() {
        for (kind, accepted, rejected) in [
            (
                ScalarKind::Int32,
                vec!["-2147483648", "2147483647", "0"],
                vec!["-2147483649", "2147483648"],
            ),
            (
                ScalarKind::Int64,
                vec!["-9223372036854775808", "9223372036854775807", "0"],
                vec!["-9223372036854775809", "9223372036854775808"],
            ),
            (
                ScalarKind::UInt32,
                vec!["0", "4294967295"],
                vec!["-1", "4294967296"],
            ),
            (
                ScalarKind::UInt64,
                vec!["0", "18446744073709551615"],
                vec!["-1", "18446744073709551616"],
            ),
        ] {
            for value in accepted {
                let parsed = kind.parse_literal(value).unwrap();
                // All parsed boundary values produce a typed kernel literal.
                let _ = parsed.kernel_expression();
            }
            for value in rejected.into_iter().chain(["", "1.0", "not-an-integer"]) {
                assert!(kind.parse_literal(value).is_none(), "{kind:?}: {value}");
            }
        }
        assert!(ScalarKind::Bool.parse_literal("1").is_none());
    }
}
