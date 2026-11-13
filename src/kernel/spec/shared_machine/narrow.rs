//! Annotated narrow ring operations keep their native modular reading.
use super::*;

fn operand(format: MachineIntegerType, value: &SpecValue) -> Option<KernelTerm> {
    let (source, view) = value.machine()?;
    if source == format {
        return Some(retained_operand(format, view));
    }
    // Unsuffixed literals have type int32. Only literals the narrow format
    // holds are accepted, exactly as at the existing native input boundary.
    if source != MachineIntegerType::Int32 {
        return None;
    }
    let literal = view.literal()?;
    let integer = source.constant_from_term(&literal)?.to_integer();
    let word = crate::kernel::machine_integer::range::constant_word(format, &integer)?;
    Some(KernelTerm::retained_native_machine_operand(format, &word))
}

pub(super) fn apply(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: &SpecValue,
    right: &SpecValue,
) -> Option<PreparedExpression> {
    if !crate::kernel::eval::is_narrow_format(format)
        || !matches!(
            op,
            MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply
        )
    {
        return None;
    }
    let left = operand(format, left)?;
    let right = operand(format, right)?;
    let value = if let (KernelTermNode::MachineLiteral(a), KernelTermNode::MachineLiteral(b)) =
        (left.node(), right.node())
    {
        let word = MachineTerm::machine_binary(format, op, a.legacy_term(), b.legacy_term());
        KernelTerm::retained_native_machine_operand(format, &word)
    } else {
        KernelTerm::machine_binary_shared(format, op, [left, right])
    };
    // The annotation denotes modular narrow arithmetic, with no new domain.
    Some(PreparedExpression {
        value,
        obligations: Vec::new(),
    })
}
