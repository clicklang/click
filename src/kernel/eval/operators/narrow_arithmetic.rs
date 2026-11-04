//! Native 8- and 16-bit arithmetic (`design/machine-integers.md`, decisions
//! G2 and G4). A specification operator at a narrow type and a Rust operator
//! on narrow values are the operator of that type, `(a op b) mod 2^N`, built
//! as its native node over the operands as written: no promotion to `int32`
//! and no conversion back. C's narrow arithmetic is not this: it promotes,
//! and its conversion back is its own node, which the cross-format relations
//! (R-dist with R-comp) meet with the native node.
use super::*;
use crate::kernel::{MachineBinaryOp, MachineUnaryOp};
use crate::kernel::{constant_u32, int32_constant};

/// Whether `format` is an 8- or 16-bit format.
pub(in crate::kernel) fn is_narrow_format(format: MachineIntegerType) -> bool {
    matches!(
        format,
        MachineIntegerType::Int8
            | MachineIntegerType::UInt8
            | MachineIntegerType::Int16
            | MachineIntegerType::UInt16
    )
}

/// The term of `value` as an operand at the narrow `format`: a value of that
/// format, or an `int32` literal the format holds, which becomes the
/// format's constant (an unsuffixed specification literal is an `int32`).
/// One match on the value.
pub(in crate::kernel) fn narrow_operand(
    format: MachineIntegerType,
    value: &CValue,
) -> Option<MachineTerm> {
    match value {
        CValue::Int8(term) | CValue::UInt8(term) | CValue::Int16(term) | CValue::UInt16(term) => {
            (MachineIntegerType::from_c_type(value.c_type()) == Some(format)).then(|| term.clone())
        }
        CValue::Int32(int32_constant!(bits)) => {
            let value = num_bigint::BigInt::from(constant_u32(*bits) as i32);
            let (low, high) = format.format().bounds();
            (value >= low && value <= high)
                .then(|| MachineTerm::narrow_constant(format, u128::from(constant_u32(*bits))))
        }
        _ => None,
    }
}

/// `left op right` at the narrow `format`, when `op` has a native node there
/// and both operands are values of `format` (a shift count is a 32-bit
/// value, read separately as C reads it). `None` leaves the operation to the
/// caller's promoted reading.
pub(in crate::kernel) fn native_narrow_binary(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: &CValue,
    right: &CValue,
) -> Option<CValue> {
    if !is_narrow_format(format) || !crate::kernel::primitives::is_native_narrow_operator(op) {
        return None;
    }
    let left = narrow_operand(format, left)?;
    let right = if op == MachineBinaryOp::ShiftLeft {
        // A native narrow shift's count is a 32-bit word, as a 32-bit
        // shift's is, so the shift meets its promoted spelling (rule N).
        match right.numeric_value() {
            CValue::Int32(count) | CValue::UInt32(count) => count.clone(),
            _ => return None,
        }
    } else {
        narrow_operand(format, right)?
    };
    Some(format.value_from_term(MachineTerm::machine_binary(format, op, left, right)))
}

/// `~value` at the narrow `format`, when `value` is a value of that format.
pub(in crate::kernel) fn native_narrow_not(
    format: MachineIntegerType,
    value: &CValue,
) -> Option<CValue> {
    if !is_narrow_format(format) {
        return None;
    }
    Some(format.value_from_term(MachineTerm::machine_unary(
        format,
        MachineUnaryOp::BitwiseNot,
        narrow_operand(format, value)?,
    )))
}
