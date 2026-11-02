//! Shared arithmetic producers, with definedness kept outside the term.
//! Deferred operands and nested signed operations retain their old evaluator.
use super::*;

mod signed;

pub(super) struct PreparedExpression {
    pub(super) value: KernelTerm,
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn prepare(
    expression: &SpecExpression,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<PreparedExpression>> {
    if let Some(prepared) = signed::prepare(expression, budget)? {
        return Ok(Some(prepared));
    }
    Ok(
        prepare_unsigned(expression, budget)?.map(|value| PreparedExpression {
            value,
            obligations: Vec::new(),
        }),
    )
}

fn prepare_unsigned(
    expression: &SpecExpression,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<KernelTerm>> {
    enum Step<'a> {
        Enter(&'a SpecExpression),
        Binary(MachineBinaryOp),
    }
    enum Prepared<'a> {
        Value(MachineIntegerType, &'a Bitvector32Term),
        Binary(MachineIntegerType, MachineBinaryOp),
    }
    // Select the fragment once before importing any legacy payload. A rejected
    // mixed/deferred tree therefore cannot repeatedly import its large leaves.
    let mut pending = vec![Step::Enter(expression)];
    let mut formats = Vec::new();
    let mut prepared = Vec::new();
    while let Some(step) = pending.pop() {
        match step {
            Step::Enter(expression) => {
                crate::instrumentation::record_deterministic_work(1);
                if crate::kernel::assumptions::reasoning_interrupted() {
                    return Err(ExecutionLimit::Deadline);
                }
                match expression {
                    SpecExpression::Value(CValue::UInt32(value)) => {
                        formats.push(MachineIntegerType::UInt32);
                        prepared.push(Prepared::Value(MachineIntegerType::UInt32, value));
                    }
                    SpecExpression::Value(CValue::UInt64(value)) => {
                        formats.push(MachineIntegerType::UInt64);
                        prepared.push(Prepared::Value(MachineIntegerType::UInt64, value));
                    }
                    SpecExpression::Add(a, b)
                    | SpecExpression::Subtract(a, b)
                    | SpecExpression::Multiply(a, b) => {
                        let op = match expression {
                            SpecExpression::Add(..) => MachineBinaryOp::Add,
                            SpecExpression::Subtract(..) => MachineBinaryOp::Subtract,
                            _ => MachineBinaryOp::Multiply,
                        };
                        pending.push(Step::Binary(op));
                        pending.push(Step::Enter(b));
                        pending.push(Step::Enter(a));
                    }
                    _ => return Ok(None),
                }
            }
            Step::Binary(op) => {
                let right = formats.pop().unwrap();
                let left = formats.pop().unwrap();
                if left != right {
                    return Ok(None);
                }
                formats.push(left);
                prepared.push(Prepared::Binary(left, op));
            }
        }
    }
    let mut values = Vec::new();
    let mut importer = KernelTermImport::default();
    for step in prepared {
        budget.consume_expression_step()?;
        match step {
            Prepared::Value(format, value) => {
                // Match the existing 32-bit word convention at the input
                // boundary; subsequent operations retain shared children.
                let value = if format == MachineIntegerType::UInt32 {
                    CValue::UInt32(Bitvector32Term::operand32(format, value.clone()))
                } else {
                    CValue::UInt64(value.clone())
                };
                values.push(importer.argument(&PureFunctionArgument::Value(value)));
            }
            Prepared::Binary(format, op) => {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                // Preserve the existing evaluator's literal-only folding.
                // Shared node construction itself is always structural.
                let term = if matches!(left.node(), KernelTermNode::MachineLiteral(_))
                    && matches!(right.node(), KernelTermNode::MachineLiteral(_))
                {
                    let mut export = KernelTermExport::default();
                    let bits = |value| match value {
                        PureFunctionArgument::Value(
                            CValue::UInt32(bits) | CValue::UInt64(bits),
                        ) => bits,
                        _ => unreachable!(),
                    };
                    let a = bits(export.argument(&left).map_err(|_| ExecutionLimit::Paths)?);
                    let b = bits(export.argument(&right).map_err(|_| ExecutionLimit::Paths)?);
                    let value = Bitvector32Term::logical_machine_binary(format, op, a, b);
                    let value = if format == MachineIntegerType::UInt32 {
                        CValue::UInt32(value)
                    } else {
                        CValue::UInt64(value)
                    };
                    importer.argument(&PureFunctionArgument::Value(value))
                } else {
                    KernelTerm::arithmetic_binary(format, op, [left, right])
                        .map_err(|_| ExecutionLimit::Paths)?
                };
                values.push(term);
            }
        }
    }
    Ok(values.pop())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluate(expression: &SpecExpression, legacy: bool) -> Vec<SpecExpressionPath> {
        evaluate_with_assumptions(expression, legacy, &PureFactContext::new())
    }

    fn evaluate_with_assumptions(
        expression: &SpecExpression,
        legacy: bool,
        assumptions: &PureFactContext,
    ) -> Vec<SpecExpressionPath> {
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_preparation_disabled = legacy;
        evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&CState::new(), None),
            expression,
            assumptions,
            &mut budget,
        )
        .unwrap()
    }

    #[test]
    fn signed_available_operands_preserve_values_and_separate_domains() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let wrap = |bits| {
                if format == MachineIntegerType::Int32 {
                    CValue::Int32(bits)
                } else {
                    CValue::Int64(bits)
                }
            };
            let constant = |n: i64| {
                if format == MachineIntegerType::Int32 {
                    Bitvector32Term::Constant(n as u32)
                } else {
                    Bitvector32Term::Int64Constant(n)
                }
            };
            let maximum = if format == MachineIntegerType::Int32 {
                i32::MAX as i64
            } else {
                i64::MAX
            };
            let minimum = -maximum - 1;
            let variable = Bitvector32Term::Variable(Variable(990004));
            for (left, right) in [
                (variable.clone(), variable.clone()),
                (variable.clone(), constant(0)),
                (constant(2), constant(3)),
                (constant(maximum), constant(1)),
                (constant(minimum), constant(-1)),
                (constant(maximum), constant(maximum)),
            ] {
                for operator in [
                    MachineBinaryOp::Add,
                    MachineBinaryOp::Subtract,
                    MachineBinaryOp::Multiply,
                ] {
                    let a = Box::new(SpecExpression::Value(wrap(left.clone())));
                    let b = Box::new(SpecExpression::Value(wrap(right.clone())));
                    let expression = match operator {
                        MachineBinaryOp::Add => SpecExpression::Add(a, b),
                        MachineBinaryOp::Subtract => SpecExpression::Subtract(a, b),
                        _ => SpecExpression::Multiply(a, b),
                    };
                    let mut execution = ExecutionBudget::new();
                    let prepared =
                        prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                            .unwrap()
                            .unwrap();
                    if left == variable {
                        assert!(matches!(
                            prepared.value.node(),
                            KernelTermNode::MachineBinary { .. }
                        ));
                    }
                    let paths = evaluate(&expression, false);
                    assert_eq!(paths, evaluate(&expression, true));
                    // Neither overflowing literals nor symbolic operands can
                    // lose their domain just because the value is now shared.
                    if operator == MachineBinaryOp::Add
                        && ((left == variable && right == variable) || left == constant(maximum))
                    {
                        assert_eq!(paths[0].obligations.len(), 1);
                    }
                }
            }
        }
    }

    #[test]
    fn shared_signed_domains_retain_held_resource_metadata() {
        let operand = || {
            Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(990005)),
            )))
        };
        let expression = SpecExpression::Add(operand(), operand());
        for held in [false, true] {
            let assumptions = if held {
                PureFactContext::new().assume_held_resource_domains()
            } else {
                PureFactContext::new()
            };
            let shared = evaluate_with_assumptions(&expression, false, &assumptions);
            let legacy = evaluate_with_assumptions(&expression, true, &assumptions);
            assert_eq!(shared, legacy);
            assert_eq!(shared[0].obligations.len(), 1);
            // ProofObligation equality deliberately ignores this metadata.
            for path in [&shared[0], &legacy[0]] {
                assert!(path.obligations[0].evaluation_domain);
                assert_eq!(path.obligations[0].assumable, held);
            }
        }
    }

    #[test]
    fn unsigned_producers_preserve_exact_words_and_wrapping_results() {
        for format in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
            let wrap = |bits| {
                if format == MachineIntegerType::UInt32 {
                    CValue::UInt32(bits)
                } else {
                    CValue::UInt64(bits)
                }
            };
            let one = if format == MachineIntegerType::UInt32 {
                Bitvector32Term::Constant(1)
            } else {
                Bitvector32Term::UInt64Constant(1)
            };
            let maximum = if format == MachineIntegerType::UInt32 {
                Bitvector32Term::Constant(u32::MAX)
            } else {
                Bitvector32Term::UInt64Constant(u64::MAX)
            };
            for left in [Bitvector32Term::Variable(Variable(990001)), maximum] {
                for operator in [
                    MachineBinaryOp::Add,
                    MachineBinaryOp::Subtract,
                    MachineBinaryOp::Multiply,
                ] {
                    let a = Box::new(SpecExpression::Value(wrap(left.clone())));
                    let b = Box::new(SpecExpression::Value(wrap(one.clone())));
                    let expression = match operator {
                        MachineBinaryOp::Add => SpecExpression::Add(a, b),
                        MachineBinaryOp::Subtract => SpecExpression::Subtract(a, b),
                        _ => SpecExpression::Multiply(a, b),
                    };
                    assert_eq!(evaluate(&expression, false), evaluate(&expression, true));
                    assert!(evaluate(&expression, false)[0].obligations.is_empty());
                }
            }
        }
    }

    #[test]
    fn partial_and_deferred_arithmetic_keeps_its_obligations() {
        let signed = || {
            Box::new(SpecExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(990002)),
            )))
        };
        let unsigned = || {
            Box::new(SpecExpression::Value(CValue::UInt64(
                Bitvector32Term::Variable(Variable(990003)),
            )))
        };
        for expression in [
            SpecExpression::Add(signed(), signed()),
            SpecExpression::Add(Box::new(SpecExpression::Add(signed(), signed())), signed()),
            SpecExpression::Divide(unsigned(), unsigned()),
            SpecExpression::ShiftLeft(unsigned(), unsigned()),
            SpecExpression::Multiply(unsigned(), signed()),
        ] {
            assert_eq!(evaluate(&expression, false), evaluate(&expression, true));
        }
        let signed_sum = SpecExpression::Add(signed(), signed());
        assert!(!evaluate(&signed_sum, false)[0].obligations.is_empty());
        let zero = || {
            Box::new(SpecExpression::Value(CValue::UInt64(
                Bitvector32Term::UInt64Constant(0),
            )))
        };
        let nested =
            SpecExpression::Multiply(zero(), Box::new(SpecExpression::Divide(unsigned(), zero())));
        let paths = evaluate(&nested, false);
        assert_eq!(paths, evaluate(&nested, true));
        assert!(!paths[0].obligations.is_empty());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/shared_machine.rs");
}
