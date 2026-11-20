//! The supported 128-bit logical operators retain their mathematical source
//! and domain. Operand equalities cannot replace that source during lowering.
use super::*;
use crate::kernel::machine_integer::wide_spec;

pub(super) fn apply(
    op: MachineBinaryOp,
    a: MachineIntegerType,
    left: MachineOperandView<'_>,
    b: MachineIntegerType,
    right: MachineOperandView<'_>,
    budget: &SpecEvaluation<'_>,
) -> Option<PreparedExpression> {
    let destination = wide_spec::result_type(op, a, b)?;
    let left = left.observe(a)?;
    let right = right.observe(b)?;
    let (result, obligation) =
        wide_spec::result_and_domain(op, SpecDivision::of(budget), destination, left, right);
    let value = if let Some(term) = result.as_const().and_then(|constant| {
        crate::kernel::machine_integer::range::constant_word(destination, constant)
    }) {
        KernelTermImport::default().machine(destination, &term)
    } else {
        let integer = KernelTermImport::default().integer(&result.into());
        KernelTerm::integer_to_machine(destination, integer).expect("Integer source")
    };
    Some(PreparedExpression {
        value,
        obligations: obligation.into_iter().collect(),
    })
}
