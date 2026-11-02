//! One signed operation over available values. Nested signed operations must
//! wait for shared obligation operands: exporting every prefix into an Integer
//! machine observation would repeatedly copy the growing expression.
use super::*;

pub(super) fn prepare(
    expression: &SpecExpression,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<PreparedExpression>> {
    let (op, left, right) = match expression {
        SpecExpression::Add(a, b) => (MachineBinaryOp::Add, a, b),
        SpecExpression::Subtract(a, b) => (MachineBinaryOp::Subtract, a, b),
        SpecExpression::Multiply(a, b) => (MachineBinaryOp::Multiply, a, b),
        _ => return Ok(None),
    };
    let (format, left, right) = match (left.as_ref(), right.as_ref()) {
        (SpecExpression::Value(CValue::Int32(a)), SpecExpression::Value(CValue::Int32(b))) => {
            (MachineIntegerType::Int32, a, b)
        }
        (SpecExpression::Value(CValue::Int64(a)), SpecExpression::Value(CValue::Int64(b))) => {
            (MachineIntegerType::Int64, a, b)
        }
        _ => return Ok(None),
    };
    // Charge the two available operands and the operation, just as the legacy
    // evaluator does. Selection above inspects only these three source nodes.
    for _ in 0..3 {
        crate::instrumentation::record_deterministic_work(1);
        if crate::kernel::assumptions::reasoning_interrupted() {
            return Err(ExecutionLimit::Deadline);
        }
        budget.consume_expression_step()?;
    }
    let obligations = Proposition::arithmetic_domain([Proposition::signed_arithmetic_domain(
        format, op, left, right,
    )])
    .map(|domain| {
        ProofObligation::evaluation_domain(domain).with_context("arithmetic expression is defined")
    })
    .into_iter()
    .collect();

    let wrap = |value| {
        if format == MachineIntegerType::Int32 {
            CValue::Int32(value)
        } else {
            CValue::Int64(value)
        }
    };
    let mut importer = KernelTermImport::default();
    let operand = |value: &Bitvector32Term| {
        wrap(if format == MachineIntegerType::Int32 {
            Bitvector32Term::operand32(format, value.clone())
        } else {
            value.clone()
        })
    };
    let a = importer.argument(&PureFunctionArgument::Value(operand(left)));
    let b = importer.argument(&PureFunctionArgument::Value(operand(right)));
    let value = if matches!(a.node(), KernelTermNode::MachineLiteral(_))
        && matches!(b.node(), KernelTermNode::MachineLiteral(_))
    {
        // Literal evaluation belongs to the evaluator, not the structural
        // constructor. Even an overflowing result retains its domain above.
        importer.argument(&PureFunctionArgument::Value(wrap(
            Bitvector32Term::logical_machine_binary(format, op, left.clone(), right.clone()),
        )))
    } else {
        KernelTerm::arithmetic_binary(format, op, [a, b]).map_err(|_| ExecutionLimit::Paths)?
    };
    Ok(Some(PreparedExpression { value, obligations }))
}
