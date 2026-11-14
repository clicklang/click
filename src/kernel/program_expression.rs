//! Constructors for the shared executable program-expression model.

use super::*;

pub fn variable(name: impl Into<String>) -> ProgramExpression {
    ProgramExpression::Variable(name.into())
}

pub fn function_address(name: impl Into<String>) -> ProgramExpression {
    ProgramExpression::FunctionAddress(name.into())
}

pub fn cast(expression: ProgramExpression, target_type: ProgramType) -> ProgramExpression {
    cast_with_pointee_volatile(expression, target_type, false)
}

pub fn cast_with_pointee_volatile(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
) -> ProgramExpression {
    cast_with_pointee_qualifiers(expression, target_type, pointee_volatile, false)
}

pub fn cast_with_pointee_qualifiers(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
    pointee_constant: bool,
) -> ProgramExpression {
    cast_with_pointee_qualifiers_and_struct(
        expression,
        target_type,
        pointee_volatile,
        pointee_constant,
        None,
    )
}

pub fn cast_with_pointee_qualifiers_and_struct(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
    pointee_constant: bool,
    pointee_struct: Option<String>,
) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: crate::kernel::IntegerCastMode::Standard,
        pointee_struct,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: false,
    }
}

/// A cast the C source wrote. Its result has exactly the destination's
/// pointee `const` qualification, so unlike the lowering-inserted casts
/// above it can drop the source pointer's `const`.
pub fn c_source_cast_with_pointee_qualifiers_and_struct(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
    pointee_constant: bool,
    pointee_struct: Option<String>,
) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: crate::kernel::IntegerCastMode::Standard,
        pointee_struct,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: true,
    }
}

/// Marks a cast lowered from C source as C's integer conversion
/// (`IntegerCastMode::CConversion`). Any other cast is returned unchanged.
pub fn c_source_integer_conversion(mut expression: ProgramExpression) -> ProgramExpression {
    if let ProgramExpression::Cast { integer_mode, .. } = &mut expression
        && *integer_mode == IntegerCastMode::Standard
    {
        *integer_mode = IntegerCastMode::CConversion;
    }
    expression
}

/// Explicit modulo conversion between admitted machine integer types.
/// The evaluator checks both runtime types. This policy is shared by Rust and
/// C++20; C source conversions use `c_source_integer_conversion`, and a
/// specification's casts keep `cast` and its checked policy.
pub fn integer_cast_modulo(
    expression: ProgramExpression,
    target_type: ProgramType,
) -> ProgramExpression {
    let mut result = cast(expression, target_type);
    if let ProgramExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = IntegerCastMode::Modulo;
    }
    result
}

/// The `Bool` value of a Rust comparison, `!` or connective (decision D5):
/// the condition itself, with no path split.
pub fn bool_value(expression: ProgramExpression) -> ProgramExpression {
    let mut result = cast(expression, ProgramType::Bool);
    if let ProgramExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = IntegerCastMode::BoolValue;
    }
    result
}

/// A Rust operator on 8- or 16-bit operands at their type `target_type`
/// (decision G4): `operation` is the operator over the operands as written,
/// and its value is the native node of that type, with no promotion.
pub fn narrow_arithmetic(
    operation: ProgramExpression,
    target_type: ProgramType,
) -> ProgramExpression {
    let mut result = cast(operation, target_type);
    if let ProgramExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = IntegerCastMode::NarrowArithmetic;
    }
    result
}

/// The C++20 uint64-to-int64 rule, distinct from an ordinary C cast.
pub fn uint64_bits_to_int64(expression: ProgramExpression) -> ProgramExpression {
    let mut result = cast(expression, ProgramType::Int64);
    if let ProgramExpression::Cast { integer_mode, .. } = &mut result {
        *integer_mode = IntegerCastMode::UInt64BitsToInt64;
    }
    result
}

pub fn conditional(
    condition: ProgramExpression,
    then_branch: ProgramExpression,
    else_branch: ProgramExpression,
) -> ProgramExpression {
    ProgramExpression::Conditional {
        condition: Box::new(condition),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn float_classification(
    expression: ProgramExpression,
    classification: FloatClassification,
) -> ProgramExpression {
    ProgramExpression::FloatClassification {
        expression: Box::new(expression),
        classification,
    }
}

pub fn float_negate(expression: ProgramExpression) -> ProgramExpression {
    ProgramExpression::FloatNegate(Box::new(expression))
}

pub fn addr_of(name: impl Into<String>) -> ProgramExpression {
    ProgramExpression::AddressOf(Box::new(variable(name)))
}

/// A non-reading check of the storage denoted by an lvalue.
pub fn checked_object_address(lvalue: ProgramExpression) -> ProgramExpression {
    ProgramExpression::CheckedObjectAddress(Box::new(lvalue))
}

pub fn pointer_offset_bytes(pointer: ProgramExpression, bytes: u32) -> ProgramExpression {
    if bytes == 0 {
        pointer
    } else {
        ProgramExpression::PointerOffsetBytes {
            pointer: Box::new(pointer),
            bytes,
        }
    }
}

pub fn int32_literal(value: u32) -> ProgramExpression {
    ProgramExpression::Value(int32(MachineTerm::constant(value)))
}

pub fn uint8_literal(value: u8) -> ProgramExpression {
    ProgramExpression::Value(uint8(MachineTerm::constant(u32::from(value))))
}

pub fn uint32_literal(value: u32) -> ProgramExpression {
    ProgramExpression::Value(uint32(MachineTerm::constant(value)))
}

/// Signed wide literal in the common checked machine arena.
pub fn int128_literal(value: i128) -> ProgramExpression {
    let ty = MachineIntegerType::Int128;
    ProgramExpression::Value(
        ty.constant_value(
            MachineIntegerConstant::from_signed(ty.format(), value)
                .expect("i128 fits the signed 128-bit format"),
        )
        .expect("exact wide format"),
    )
}

/// Unsigned wide literal; the high 64 bits are retained.
pub fn uint128_literal(value: u128) -> ProgramExpression {
    let ty = MachineIntegerType::UInt128;
    ProgramExpression::Value(
        ty.constant_value(
            MachineIntegerConstant::from_unsigned(ty.format(), value)
                .expect("u128 fits the unsigned 128-bit format"),
        )
        .expect("exact wide format"),
    )
}

pub fn int64_literal(value: i64) -> ProgramExpression {
    ProgramExpression::Value(int64(MachineTerm::int64_constant(value)))
}

pub fn uint64_literal(value: u64) -> ProgramExpression {
    ProgramExpression::Value(uint64(MachineTerm::uint64_constant(value)))
}

pub fn float32_literal(bits: u32) -> ProgramExpression {
    ProgramExpression::Value(float32(MachineTerm::constant(bits)))
}

pub fn float64_literal(bits: u64) -> ProgramExpression {
    ProgramExpression::Value(float64(MachineTerm::uint64_constant(bits)))
}

pub fn pointer_value(pointer: Pointer) -> ProgramExpression {
    ProgramExpression::Value(ProgramValue::pointer(pointer))
}

pub fn typed_pointer_value(pointer: Pointer, c_type: ProgramType) -> ProgramExpression {
    ProgramExpression::Value(ProgramValue::typed_pointer(pointer, c_type))
}

pub fn less_than(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn less_equal(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn greater_than(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn greater_equal(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn equal(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Equal(Box::new(left), Box::new(right))
}

pub fn not_equal(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn not(expression: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Not(Box::new(expression))
}

pub fn and(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::And(Box::new(left), Box::new(right))
}

pub fn or(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Or(Box::new(left), Box::new(right))
}

pub fn add(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Add(Box::new(left), Box::new(right))
}

pub fn subtract(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn multiply(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Multiply(Box::new(left), Box::new(right))
}

pub fn divide(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Divide(Box::new(left), Box::new(right))
}

pub fn remainder(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Remainder(Box::new(left), Box::new(right))
}

pub fn shift_left(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::ShiftLeft(Box::new(left), Box::new(right))
}

pub fn shift_right(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::ShiftRight(Box::new(left), Box::new(right))
}

pub fn bitwise_and(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::BitwiseAnd(Box::new(left), Box::new(right))
}

pub fn bitwise_or(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::BitwiseOr(Box::new(left), Box::new(right))
}

pub fn bitwise_xor(left: ProgramExpression, right: ProgramExpression) -> ProgramExpression {
    ProgramExpression::BitwiseXor(Box::new(left), Box::new(right))
}

pub fn bitwise_not(expression: ProgramExpression) -> ProgramExpression {
    ProgramExpression::BitwiseNot(Box::new(expression))
}

pub fn load(pointer: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Load(Box::new(pointer))
}

pub fn typed_load(pointer: ProgramExpression, value_type: ProgramType) -> ProgramExpression {
    typed_load_with_source(pointer, value_type, None)
}

pub(crate) fn typed_load_with_source(
    pointer: ProgramExpression,
    value_type: ProgramType,
    source: Option<crate::kernel::LoadSourceId>,
) -> ProgramExpression {
    qualified_typed_load_with_source(pointer, value_type, false, None, source)
}

pub(crate) fn qualified_typed_load_with_source(
    pointer: ProgramExpression,
    value_type: ProgramType,
    pointee_constant: bool,
    access_class: Option<crate::kernel::effective_type::CAccessClass>,
    source: Option<crate::kernel::LoadSourceId>,
) -> ProgramExpression {
    ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: false,
        pointee_constant,
        access_class,
        source: source
            .map(crate::kernel::ExpressionLoadSource::new)
            .unwrap_or_default(),
    }
}

/// A load of a `value_type` lvalue whose access class the kernel type cannot
/// give (`design/effective-types.md`).
pub(crate) fn classed_load(
    pointer: ProgramExpression,
    value_type: ProgramType,
    access_class: Option<crate::kernel::effective_type::CAccessClass>,
) -> ProgramExpression {
    ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: false,
        pointee_constant: false,
        access_class,
        source: crate::kernel::ExpressionLoadSource::none(),
    }
}

pub(crate) fn qualified_volatile_typed_load(
    pointer: ProgramExpression,
    value_type: ProgramType,
    pointee_constant: bool,
) -> ProgramExpression {
    ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: true,
        pointee_constant,
        access_class: None,
        source: crate::kernel::ExpressionLoadSource::none(),
    }
}

pub fn index(base: ProgramExpression, index: ProgramExpression) -> ProgramExpression {
    ProgramExpression::Index(Box::new(base), Box::new(index))
}
