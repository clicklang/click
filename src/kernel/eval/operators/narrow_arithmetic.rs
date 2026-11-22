//! Native 8- and 16-bit arithmetic (`design/machine-integers.md`, decisions
//! G2 and G4). Supported native operators build `(a op b) mod 2^N` over the
//! operands as written. Rust signed division and remainder use a promoted
//! term with a narrow safety check. C's narrow arithmetic promotes,
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
    value: &ProgramValue,
) -> Option<MachineTerm> {
    match value {
        ProgramValue::Int8(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::Int16(term)
        | ProgramValue::UInt16(term) => {
            (MachineIntegerType::from_program_type(value.program_type()) == Some(format))
                .then(|| term.clone())
        }
        ProgramValue::Int32(int32_constant!(bits)) => {
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
    left: &ProgramValue,
    right: &ProgramValue,
) -> Option<ProgramValue> {
    if !is_narrow_format(format) || !crate::kernel::primitives::is_native_narrow_operator(op) {
        return None;
    }
    let left = narrow_operand(format, left)?;
    let right = if op == MachineBinaryOp::ShiftLeft {
        // A native narrow shift's count is a 32-bit word, as a 32-bit
        // shift's is, so the shift meets its promoted spelling (rule N).
        match right.numeric_value() {
            ProgramValue::Int32(count) | ProgramValue::UInt32(count) => count.clone(),
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
    value: &ProgramValue,
) -> Option<ProgramValue> {
    if !is_narrow_format(format) {
        return None;
    }
    Some(format.value_from_term(MachineTerm::machine_unary(
        format,
        MachineUnaryOp::BitwiseNot,
        narrow_operand(format, value)?,
    )))
}

/// Rust retains the promoted operation's term. The narrow MIN/-1 exclusion
/// both enforces the panic check and certifies the exact result conversion
/// on the normal path of the promoted operation. Neither result can exceed
/// the dividend's magnitude. A quotient can negate the minimum at divisor
/// -1, the only way to exceed the positive endpoint.
pub(in crate::kernel) fn apply_rust_narrow_signed_division(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: ProgramValue,
    right: ProgramValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    use crate::kernel::machine_integer::conversion;
    let (Some(left), Some(right)) = (
        narrow_operand(format, &left),
        narrow_operand(format, &right),
    ) else {
        return vec![program_type_mismatch_expression_path(facts, obligations)];
    };
    let safe = Proposition::signed_division_exclusion(format, &left, &right);
    let widen = |operand| conversion::convert_term(format, MachineIntegerType::Int32, operand);
    let (left, right) = (widen(left), widen(right));
    let (mut paths, label) = match op {
        MachineBinaryOp::Divide => (
            apply_program_int32_divide(left, right, facts, obligations, assumptions),
            "Rust div panic check",
        ),
        MachineBinaryOp::Remainder => (
            apply_program_int32_remainder(left, right, facts, obligations, assumptions),
            "Rust rem panic check",
        ),
        _ => unreachable!("narrow signed division operator"),
    };
    for path in &mut paths {
        let ExpressionOutcome::Value(source @ ProgramValue::Int32(term)) = &path.outcome else {
            continue;
        };
        path.obligations.push(
            ProofObligation::verification_condition(safe.clone())
                .with_statement_entry_required(true)
                .with_context(label),
        );
        let result = format.value_from_term(conversion::convert_term(
            MachineIntegerType::Int32,
            format,
            term.clone(),
        ));
        path.facts.extend(
            super::super::expression::checked_narrowing_identity(source, &result)
                .into_iter()
                .map(ExecutionPureFact::certified),
        );
        path.outcome = ExpressionOutcome::Value(result);
    }
    paths
}
