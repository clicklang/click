//! The arithmetic shape of a [`Bitvector32Term`]: which operator a node
//! applies and to which operands. Traversals that rebuild or describe every
//! node keep their own arms for the variants they treat specially and handle
//! the uniform arithmetic variants through this split and its rebuild.

use super::*;

/// A two-operand arithmetic [`Bitvector32Term`] operator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BitvectorBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    UnsignedDivide,
    Remainder,
    UnsignedRemainder,
    ShiftLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    Int64Add,
    Int64Subtract,
    Int64Multiply,
    Int64Divide,
    Int64Remainder,
    Int64ShiftLeft,
    Int64ArithmeticShiftRight,
    Int64BitwiseAnd,
    Int64BitwiseOr,
    Int64BitwiseXor,
    UInt64Add,
    UInt64Subtract,
    UInt64Multiply,
    UInt64Divide,
    UInt64Remainder,
    UInt64ShiftLeft,
    UInt64LogicalShiftRight,
    UInt64BitwiseAnd,
    UInt64BitwiseOr,
    UInt64BitwiseXor,
    Float32(CFloatBinaryOperator),
    Float64(CFloatBinaryOperator),
}

/// A one-operand arithmetic [`Bitvector32Term`] operator or conversion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BitvectorUnaryOp {
    BitwiseNot,
    Int64BitwiseNot,
    UInt64BitwiseNot,
    Int64From32,
    UInt64From32,
    UInt32From64,
    Int64FromUInt32,
    UInt64FromInt32,
    UInt64FromInt64,
    Float32Negate,
    Float64Negate,
    MachineIntegerCast {
        source: MachineIntegerType,
        destination: MachineIntegerType,
    },
}

impl Bitvector32Term {
    /// The operator and operands of a two-operand arithmetic node, or `None`
    /// for every other variant.
    pub(crate) fn as_binary(&self) -> Option<(BitvectorBinaryOp, &Self, &Self)> {
        match self {
            Self::Add(left, right) => Some((BitvectorBinaryOp::Add, left, right)),
            Self::Subtract(left, right) => Some((BitvectorBinaryOp::Subtract, left, right)),
            Self::Multiply(left, right) => Some((BitvectorBinaryOp::Multiply, left, right)),
            Self::Divide(left, right) => Some((BitvectorBinaryOp::Divide, left, right)),
            Self::UnsignedDivide(left, right) => {
                Some((BitvectorBinaryOp::UnsignedDivide, left, right))
            }
            Self::Remainder(left, right) => Some((BitvectorBinaryOp::Remainder, left, right)),
            Self::UnsignedRemainder(left, right) => {
                Some((BitvectorBinaryOp::UnsignedRemainder, left, right))
            }
            Self::ShiftLeft(left, right) => Some((BitvectorBinaryOp::ShiftLeft, left, right)),
            Self::ArithmeticShiftRight(left, right) => {
                Some((BitvectorBinaryOp::ArithmeticShiftRight, left, right))
            }
            Self::LogicalShiftRight(left, right) => {
                Some((BitvectorBinaryOp::LogicalShiftRight, left, right))
            }
            Self::BitwiseAnd(left, right) => Some((BitvectorBinaryOp::BitwiseAnd, left, right)),
            Self::BitwiseOr(left, right) => Some((BitvectorBinaryOp::BitwiseOr, left, right)),
            Self::BitwiseXor(left, right) => Some((BitvectorBinaryOp::BitwiseXor, left, right)),
            Self::Int64Add(left, right) => Some((BitvectorBinaryOp::Int64Add, left, right)),
            Self::Int64Subtract(left, right) => {
                Some((BitvectorBinaryOp::Int64Subtract, left, right))
            }
            Self::Int64Multiply(left, right) => {
                Some((BitvectorBinaryOp::Int64Multiply, left, right))
            }
            Self::Int64Divide(left, right) => Some((BitvectorBinaryOp::Int64Divide, left, right)),
            Self::Int64Remainder(left, right) => {
                Some((BitvectorBinaryOp::Int64Remainder, left, right))
            }
            Self::Int64ShiftLeft(left, right) => {
                Some((BitvectorBinaryOp::Int64ShiftLeft, left, right))
            }
            Self::Int64ArithmeticShiftRight(left, right) => {
                Some((BitvectorBinaryOp::Int64ArithmeticShiftRight, left, right))
            }
            Self::Int64BitwiseAnd(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseAnd, left, right))
            }
            Self::Int64BitwiseOr(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseOr, left, right))
            }
            Self::Int64BitwiseXor(left, right) => {
                Some((BitvectorBinaryOp::Int64BitwiseXor, left, right))
            }
            Self::UInt64Add(left, right) => Some((BitvectorBinaryOp::UInt64Add, left, right)),
            Self::UInt64Subtract(left, right) => {
                Some((BitvectorBinaryOp::UInt64Subtract, left, right))
            }
            Self::UInt64Multiply(left, right) => {
                Some((BitvectorBinaryOp::UInt64Multiply, left, right))
            }
            Self::UInt64Divide(left, right) => Some((BitvectorBinaryOp::UInt64Divide, left, right)),
            Self::UInt64Remainder(left, right) => {
                Some((BitvectorBinaryOp::UInt64Remainder, left, right))
            }
            Self::UInt64ShiftLeft(left, right) => {
                Some((BitvectorBinaryOp::UInt64ShiftLeft, left, right))
            }
            Self::UInt64LogicalShiftRight(left, right) => {
                Some((BitvectorBinaryOp::UInt64LogicalShiftRight, left, right))
            }
            Self::UInt64BitwiseAnd(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseAnd, left, right))
            }
            Self::UInt64BitwiseOr(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseOr, left, right))
            }
            Self::UInt64BitwiseXor(left, right) => {
                Some((BitvectorBinaryOp::UInt64BitwiseXor, left, right))
            }
            Self::Float32Binary {
                operator,
                left,
                right,
            } => Some((BitvectorBinaryOp::Float32(*operator), left, right)),
            Self::Float64Binary {
                operator,
                left,
                right,
            } => Some((BitvectorBinaryOp::Float64(*operator), left, right)),
            Self::Constant(_)
            | Self::Int64Constant(_)
            | Self::UInt64Constant(_)
            | Self::MachineIntegerConstant(_)
            | Self::Variable(_)
            | Self::If { .. }
            | Self::RangeFold { .. }
            | Self::PureFunctionApplication { .. }
            | Self::ClickFunctionApplication { .. }
            | Self::AlgebraicMatch { .. }
            | Self::MemoryLoad(..)
            | Self::PointerAddress(_)
            | Self::IntegerToMachine { .. }
            | Self::BitwiseNot(_)
            | Self::Int64BitwiseNot(_)
            | Self::UInt64BitwiseNot(_)
            | Self::Int64From32(_)
            | Self::UInt64From32(_)
            | Self::UInt32From64(_)
            | Self::Int64FromUInt32(_)
            | Self::UInt64FromInt32(_)
            | Self::UInt64FromInt64(_)
            | Self::Float32Negate(_)
            | Self::Float64Negate(_)
            | Self::MachineIntegerCast { .. } => None,
        }
    }

    /// The operator and operand of a one-operand arithmetic node or
    /// conversion, or `None` for every other variant.
    pub(crate) fn as_unary(&self) -> Option<(BitvectorUnaryOp, &Self)> {
        match self {
            Self::BitwiseNot(value) => Some((BitvectorUnaryOp::BitwiseNot, value)),
            Self::Int64BitwiseNot(value) => Some((BitvectorUnaryOp::Int64BitwiseNot, value)),
            Self::UInt64BitwiseNot(value) => Some((BitvectorUnaryOp::UInt64BitwiseNot, value)),
            Self::Int64From32(value) => Some((BitvectorUnaryOp::Int64From32, value)),
            Self::UInt64From32(value) => Some((BitvectorUnaryOp::UInt64From32, value)),
            Self::UInt32From64(value) => Some((BitvectorUnaryOp::UInt32From64, value)),
            Self::Int64FromUInt32(value) => Some((BitvectorUnaryOp::Int64FromUInt32, value)),
            Self::UInt64FromInt32(value) => Some((BitvectorUnaryOp::UInt64FromInt32, value)),
            Self::UInt64FromInt64(value) => Some((BitvectorUnaryOp::UInt64FromInt64, value)),
            Self::Float32Negate(value) => Some((BitvectorUnaryOp::Float32Negate, value)),
            Self::Float64Negate(value) => Some((BitvectorUnaryOp::Float64Negate, value)),
            Self::MachineIntegerCast {
                value,
                source,
                destination,
            } => Some((
                BitvectorUnaryOp::MachineIntegerCast {
                    source: *source,
                    destination: *destination,
                },
                value,
            )),
            Self::Constant(_)
            | Self::Int64Constant(_)
            | Self::UInt64Constant(_)
            | Self::MachineIntegerConstant(_)
            | Self::Variable(_)
            | Self::If { .. }
            | Self::RangeFold { .. }
            | Self::PureFunctionApplication { .. }
            | Self::ClickFunctionApplication { .. }
            | Self::AlgebraicMatch { .. }
            | Self::MemoryLoad(..)
            | Self::PointerAddress(_)
            | Self::IntegerToMachine { .. }
            | crate::kernel::binary_machine_term!(_, _)
            | Self::Float32Binary { .. }
            | Self::Float64Binary { .. } => None,
        }
    }
}

impl BitvectorBinaryOp {
    /// Applies the operator through its smart constructor.
    pub(crate) fn build(self, left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
        match self {
            Self::Add => Bitvector32Term::add(left, right),
            Self::Subtract => Bitvector32Term::subtract(left, right),
            Self::Multiply => Bitvector32Term::multiply(left, right),
            Self::Divide => Bitvector32Term::divide(left, right),
            Self::UnsignedDivide => Bitvector32Term::unsigned_divide(left, right),
            Self::Remainder => Bitvector32Term::remainder(left, right),
            Self::UnsignedRemainder => Bitvector32Term::unsigned_remainder(left, right),
            Self::ShiftLeft => Bitvector32Term::shift_left(left, right),
            Self::ArithmeticShiftRight => Bitvector32Term::arithmetic_shift_right(left, right),
            Self::LogicalShiftRight => Bitvector32Term::logical_shift_right(left, right),
            Self::BitwiseAnd => Bitvector32Term::bitwise_and(left, right),
            Self::BitwiseOr => Bitvector32Term::bitwise_or(left, right),
            Self::BitwiseXor => Bitvector32Term::bitwise_xor(left, right),
            Self::Int64Add => Bitvector32Term::int64_add(left, right),
            Self::Int64Subtract => Bitvector32Term::int64_subtract(left, right),
            Self::Int64Multiply => Bitvector32Term::int64_multiply(left, right),
            Self::Int64Divide => Bitvector32Term::int64_divide(left, right),
            Self::Int64Remainder => Bitvector32Term::int64_remainder(left, right),
            Self::Int64ShiftLeft => Bitvector32Term::int64_shift_left(left, right),
            Self::Int64ArithmeticShiftRight => {
                Bitvector32Term::int64_arithmetic_shift_right(left, right)
            }
            Self::Int64BitwiseAnd => Bitvector32Term::int64_bitwise_and(left, right),
            Self::Int64BitwiseOr => Bitvector32Term::int64_bitwise_or(left, right),
            Self::Int64BitwiseXor => Bitvector32Term::int64_bitwise_xor(left, right),
            Self::UInt64Add => Bitvector32Term::uint64_add(left, right),
            Self::UInt64Subtract => Bitvector32Term::uint64_subtract(left, right),
            Self::UInt64Multiply => Bitvector32Term::uint64_multiply(left, right),
            Self::UInt64Divide => Bitvector32Term::uint64_divide(left, right),
            Self::UInt64Remainder => Bitvector32Term::uint64_remainder(left, right),
            Self::UInt64ShiftLeft => Bitvector32Term::uint64_shift_left(left, right),
            Self::UInt64LogicalShiftRight => {
                Bitvector32Term::uint64_logical_shift_right(left, right)
            }
            Self::UInt64BitwiseAnd => Bitvector32Term::uint64_bitwise_and(left, right),
            Self::UInt64BitwiseOr => Bitvector32Term::uint64_bitwise_or(left, right),
            Self::UInt64BitwiseXor => Bitvector32Term::uint64_bitwise_xor(left, right),
            Self::Float32(operator) => Bitvector32Term::float32_binary(left, right, operator),
            Self::Float64(operator) => Bitvector32Term::float64_binary(left, right, operator),
        }
    }

    /// Applies the operator as the bare node, without folding or
    /// normalization. Test-only until a traversal that builds bare nodes is
    /// converted to this split.
    #[cfg(test)]
    pub(crate) fn build_raw(
        self,
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Bitvector32Term {
        let (left, right) = (Box::new(left), Box::new(right));
        match self {
            Self::Add => Bitvector32Term::Add(left, right),
            Self::Subtract => Bitvector32Term::Subtract(left, right),
            Self::Multiply => Bitvector32Term::Multiply(left, right),
            Self::Divide => Bitvector32Term::Divide(left, right),
            Self::UnsignedDivide => Bitvector32Term::UnsignedDivide(left, right),
            Self::Remainder => Bitvector32Term::Remainder(left, right),
            Self::UnsignedRemainder => Bitvector32Term::UnsignedRemainder(left, right),
            Self::ShiftLeft => Bitvector32Term::ShiftLeft(left, right),
            Self::ArithmeticShiftRight => Bitvector32Term::ArithmeticShiftRight(left, right),
            Self::LogicalShiftRight => Bitvector32Term::LogicalShiftRight(left, right),
            Self::BitwiseAnd => Bitvector32Term::BitwiseAnd(left, right),
            Self::BitwiseOr => Bitvector32Term::BitwiseOr(left, right),
            Self::BitwiseXor => Bitvector32Term::BitwiseXor(left, right),
            Self::Int64Add => Bitvector32Term::Int64Add(left, right),
            Self::Int64Subtract => Bitvector32Term::Int64Subtract(left, right),
            Self::Int64Multiply => Bitvector32Term::Int64Multiply(left, right),
            Self::Int64Divide => Bitvector32Term::Int64Divide(left, right),
            Self::Int64Remainder => Bitvector32Term::Int64Remainder(left, right),
            Self::Int64ShiftLeft => Bitvector32Term::Int64ShiftLeft(left, right),
            Self::Int64ArithmeticShiftRight => {
                Bitvector32Term::Int64ArithmeticShiftRight(left, right)
            }
            Self::Int64BitwiseAnd => Bitvector32Term::Int64BitwiseAnd(left, right),
            Self::Int64BitwiseOr => Bitvector32Term::Int64BitwiseOr(left, right),
            Self::Int64BitwiseXor => Bitvector32Term::Int64BitwiseXor(left, right),
            Self::UInt64Add => Bitvector32Term::UInt64Add(left, right),
            Self::UInt64Subtract => Bitvector32Term::UInt64Subtract(left, right),
            Self::UInt64Multiply => Bitvector32Term::UInt64Multiply(left, right),
            Self::UInt64Divide => Bitvector32Term::UInt64Divide(left, right),
            Self::UInt64Remainder => Bitvector32Term::UInt64Remainder(left, right),
            Self::UInt64ShiftLeft => Bitvector32Term::UInt64ShiftLeft(left, right),
            Self::UInt64LogicalShiftRight => Bitvector32Term::UInt64LogicalShiftRight(left, right),
            Self::UInt64BitwiseAnd => Bitvector32Term::UInt64BitwiseAnd(left, right),
            Self::UInt64BitwiseOr => Bitvector32Term::UInt64BitwiseOr(left, right),
            Self::UInt64BitwiseXor => Bitvector32Term::UInt64BitwiseXor(left, right),
            Self::Float32(operator) => Bitvector32Term::Float32Binary {
                operator,
                left,
                right,
            },
            Self::Float64(operator) => Bitvector32Term::Float64Binary {
                operator,
                left,
                right,
            },
        }
    }
}

impl BitvectorUnaryOp {
    /// Applies the operator through its smart constructor.
    pub(crate) fn build(self, value: Bitvector32Term) -> Bitvector32Term {
        match self {
            Self::BitwiseNot => Bitvector32Term::bitwise_not(value),
            Self::Int64BitwiseNot => Bitvector32Term::int64_bitwise_not(value),
            Self::UInt64BitwiseNot => Bitvector32Term::uint64_bitwise_not(value),
            Self::Int64From32 => Bitvector32Term::int64_from_32(value),
            Self::UInt64From32 => Bitvector32Term::uint64_from_32(value),
            Self::UInt32From64 => Bitvector32Term::uint32_from_64(value),
            Self::Int64FromUInt32 => Bitvector32Term::int64_from_uint32(value),
            Self::UInt64FromInt32 => Bitvector32Term::uint64_from_int32(value),
            Self::UInt64FromInt64 => Bitvector32Term::uint64_from_int64(value),
            Self::Float32Negate => Bitvector32Term::float32_negate(value),
            Self::Float64Negate => Bitvector32Term::float64_negate(value),
            Self::MachineIntegerCast {
                source,
                destination,
            } => Bitvector32Term::machine_integer_cast(source, destination, value),
        }
    }

    /// Applies the operator as the bare node, without folding or
    /// normalization. Test-only until a traversal that builds bare nodes is
    /// converted to this split.
    #[cfg(test)]
    pub(crate) fn build_raw(self, value: Bitvector32Term) -> Bitvector32Term {
        let value = Box::new(value);
        match self {
            Self::BitwiseNot => Bitvector32Term::BitwiseNot(value),
            Self::Int64BitwiseNot => Bitvector32Term::Int64BitwiseNot(value),
            Self::UInt64BitwiseNot => Bitvector32Term::UInt64BitwiseNot(value),
            Self::Int64From32 => Bitvector32Term::Int64From32(value),
            Self::UInt64From32 => Bitvector32Term::UInt64From32(value),
            Self::UInt32From64 => Bitvector32Term::UInt32From64(value),
            Self::Int64FromUInt32 => Bitvector32Term::Int64FromUInt32(value),
            Self::UInt64FromInt32 => Bitvector32Term::UInt64FromInt32(value),
            Self::UInt64FromInt64 => Bitvector32Term::UInt64FromInt64(value),
            Self::Float32Negate => Bitvector32Term::Float32Negate(value),
            Self::Float64Negate => Bitvector32Term::Float64Negate(value),
            Self::MachineIntegerCast {
                source,
                destination,
            } => Bitvector32Term::MachineIntegerCast {
                value,
                source,
                destination,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FLOAT_OPERATORS: [CFloatBinaryOperator; 4] = [
        CFloatBinaryOperator::Add,
        CFloatBinaryOperator::Subtract,
        CFloatBinaryOperator::Multiply,
        CFloatBinaryOperator::Divide,
    ];

    fn binary_ops() -> Vec<BitvectorBinaryOp> {
        let mut ops = vec![
            BitvectorBinaryOp::Add,
            BitvectorBinaryOp::Subtract,
            BitvectorBinaryOp::Multiply,
            BitvectorBinaryOp::Divide,
            BitvectorBinaryOp::UnsignedDivide,
            BitvectorBinaryOp::Remainder,
            BitvectorBinaryOp::UnsignedRemainder,
            BitvectorBinaryOp::ShiftLeft,
            BitvectorBinaryOp::ArithmeticShiftRight,
            BitvectorBinaryOp::LogicalShiftRight,
            BitvectorBinaryOp::BitwiseAnd,
            BitvectorBinaryOp::BitwiseOr,
            BitvectorBinaryOp::BitwiseXor,
            BitvectorBinaryOp::Int64Add,
            BitvectorBinaryOp::Int64Subtract,
            BitvectorBinaryOp::Int64Multiply,
            BitvectorBinaryOp::Int64Divide,
            BitvectorBinaryOp::Int64Remainder,
            BitvectorBinaryOp::Int64ShiftLeft,
            BitvectorBinaryOp::Int64ArithmeticShiftRight,
            BitvectorBinaryOp::Int64BitwiseAnd,
            BitvectorBinaryOp::Int64BitwiseOr,
            BitvectorBinaryOp::Int64BitwiseXor,
            BitvectorBinaryOp::UInt64Add,
            BitvectorBinaryOp::UInt64Subtract,
            BitvectorBinaryOp::UInt64Multiply,
            BitvectorBinaryOp::UInt64Divide,
            BitvectorBinaryOp::UInt64Remainder,
            BitvectorBinaryOp::UInt64ShiftLeft,
            BitvectorBinaryOp::UInt64LogicalShiftRight,
            BitvectorBinaryOp::UInt64BitwiseAnd,
            BitvectorBinaryOp::UInt64BitwiseOr,
            BitvectorBinaryOp::UInt64BitwiseXor,
        ];
        for operator in FLOAT_OPERATORS {
            ops.push(BitvectorBinaryOp::Float32(operator));
            ops.push(BitvectorBinaryOp::Float64(operator));
        }
        ops
    }

    fn unary_ops() -> Vec<BitvectorUnaryOp> {
        vec![
            BitvectorUnaryOp::BitwiseNot,
            BitvectorUnaryOp::Int64BitwiseNot,
            BitvectorUnaryOp::UInt64BitwiseNot,
            BitvectorUnaryOp::Int64From32,
            BitvectorUnaryOp::UInt64From32,
            BitvectorUnaryOp::UInt32From64,
            BitvectorUnaryOp::Int64FromUInt32,
            BitvectorUnaryOp::UInt64FromInt32,
            BitvectorUnaryOp::UInt64FromInt64,
            BitvectorUnaryOp::Float32Negate,
            BitvectorUnaryOp::Float64Negate,
            BitvectorUnaryOp::MachineIntegerCast {
                source: MachineIntegerType::Int32,
                destination: MachineIntegerType::UInt64,
            },
        ]
    }

    fn variable(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    #[test]
    fn every_binary_operator_splits_back_from_its_bare_node() {
        for op in binary_ops() {
            let node = op.build_raw(variable(1), variable(2));
            assert_eq!(
                node.as_binary(),
                Some((op, &variable(1), &variable(2))),
                "{op:?}"
            );
            assert_eq!(node.as_unary(), None, "{op:?}");
        }
    }

    #[test]
    fn every_unary_operator_splits_back_from_its_bare_node() {
        for op in unary_ops() {
            let node = op.build_raw(variable(1));
            assert_eq!(node.as_unary(), Some((op, &variable(1))), "{op:?}");
            assert_eq!(node.as_binary(), None, "{op:?}");
        }
    }

    /// The split covers exactly the arithmetic variants: one per binary
    /// machine operator, the two float binaries, and every unary operator
    /// and conversion. Any other variant must be handled by a traversal's
    /// own arm.
    #[test]
    fn the_split_covers_exactly_the_arithmetic_variants() {
        let others = [
            Bitvector32Term::Constant(1),
            Bitvector32Term::Int64Constant(1),
            Bitvector32Term::UInt64Constant(1),
            variable(1),
            Bitvector32Term::If {
                condition: Box::new(ConditionTerm::Constant(true)),
                then_term: Box::new(variable(1)),
                else_term: Box::new(variable(2)),
            },
            Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![variable(1)],
            },
        ];
        for term in others {
            assert_eq!(term.as_binary(), None, "{term:?}");
            assert_eq!(term.as_unary(), None, "{term:?}");
        }
        assert_eq!(binary_ops().len(), 33 + 2 * FLOAT_OPERATORS.len());
        assert_eq!(unary_ops().len(), 12);
    }

    /// `build` is the operator's smart constructor: on symbolic operands that
    /// no rule folds, it produces the same node as `build_raw`.
    #[test]
    fn smart_build_agrees_with_the_bare_node_on_unfoldable_operands() {
        for op in binary_ops() {
            let smart = op.build(variable(1), variable(2));
            let split = smart.as_binary().map(|(split_op, _, _)| split_op);
            assert_eq!(split, Some(op), "{op:?} built {smart:?}");
        }
        for op in unary_ops() {
            let smart = op.build(variable(1));
            let split = smart.as_unary().map(|(split_op, _)| split_op);
            assert_eq!(split, Some(op), "{op:?} built {smart:?}");
        }
    }
}
