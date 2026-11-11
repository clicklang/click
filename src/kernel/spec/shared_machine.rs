//! Shared arithmetic producers, with definedness kept outside the term.
//! Complete same-format arithmetic trees retain their operands in obligations.
//! Deferred and mixed-format operands retain their existing evaluator.
use super::*;

pub(super) struct PreparedExpression {
    pub(super) value: KernelTerm,
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn prepare(
    expression: &SpecExpression,
    budget: &mut SpecEvaluation<'_>,
) -> ExecutionResult<Option<PreparedExpression>> {
    enum Step<'a> {
        Enter(&'a SpecExpression),
        Binary(MachineBinaryOp),
    }
    enum Prepared<'a> {
        Value(MachineIntegerType, &'a MachineTerm),
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
                    SpecExpression::Value(CValue::Int32(value)) => {
                        formats.push(MachineIntegerType::Int32);
                        prepared.push(Prepared::Value(MachineIntegerType::Int32, value));
                    }
                    SpecExpression::Value(CValue::Int64(value)) => {
                        formats.push(MachineIntegerType::Int64);
                        prepared.push(Prepared::Value(MachineIntegerType::Int64, value));
                    }
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
    let mut obligations = Vec::new();
    let mut importer = KernelTermImport::default();
    for step in prepared {
        budget.consume_expression_step()?;
        match step {
            Prepared::Value(format, value) => {
                // Match the existing 32-bit word convention at the input
                // boundary; subsequent operations retain shared children.
                let value = if format.format().bits() == 32 {
                    MachineTerm::operand32(format, value.clone())
                } else {
                    value.clone()
                };
                // Use the machine-observation boundary, not the general term
                // importer: available bool/pure/binder payloads must retain
                // their native observation identity beneath shared arithmetic.
                values.push(KernelTerm::retained_native_machine_operand(format, &value));
            }
            Prepared::Binary(format, op) => {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                if matches!(
                    format,
                    MachineIntegerType::Int32 | MachineIntegerType::Int64
                ) && let Some(domain) =
                    Proposition::arithmetic_domain([Proposition::signed_arithmetic_domain_views(
                        format,
                        op,
                        MachineOperandView::Shared(&left),
                        MachineOperandView::Shared(&right),
                    )])
                {
                    obligations.push(
                        ProofObligation::evaluation_domain(domain)
                            .with_context("arithmetic expression is defined"),
                    );
                }
                // Preserve the existing evaluator's literal-only folding.
                // Shared node construction itself is always structural.
                let term =
                    if let (KernelTermNode::MachineLiteral(a), KernelTermNode::MachineLiteral(b)) =
                        (left.node(), right.node())
                    {
                        let a = a.legacy_term();
                        let b = b.legacy_term();
                        let value = MachineTerm::logical_machine_binary(format, op, a, b);
                        let value = wrap(format, value);
                        importer.argument(&PureFunctionArgument::Value(value))
                    } else {
                        KernelTerm::arithmetic_binary(format, op, [left, right])
                            .map_err(|_| ExecutionLimit::Paths)?
                    };
                values.push(term);
            }
        }
    }
    Ok(values
        .pop()
        .map(|value| PreparedExpression { value, obligations }))
}

fn wrap(format: MachineIntegerType, value: MachineTerm) -> CValue {
    match format {
        MachineIntegerType::Int32 => CValue::Int32(value),
        MachineIntegerType::Int64 => CValue::Int64(value),
        MachineIntegerType::UInt32 => CValue::UInt32(value),
        MachineIntegerType::UInt64 => CValue::UInt64(value),
        _ => unreachable!("prepared arithmetic format"),
    }
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
                    MachineTerm::constant(n as u32)
                } else {
                    MachineTerm::int64_constant(n)
                }
            };
            let maximum = if format == MachineIntegerType::Int32 {
                i32::MAX as i64
            } else {
                i64::MAX
            };
            let minimum = -maximum - 1;
            let variable = MachineTerm::Variable(Variable(990004));
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
    fn nested_signed_operations_preserve_obligations_in_evaluation_order() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let leaf = |n| {
                Box::new(SpecExpression::Value(wrap(
                    format,
                    MachineTerm::Variable(Variable(n)),
                )))
            };
            for expression in [
                SpecExpression::Multiply(
                    Box::new(SpecExpression::Add(leaf(990010), leaf(990011))),
                    Box::new(SpecExpression::Subtract(leaf(990012), leaf(990013))),
                ),
                SpecExpression::Subtract(
                    leaf(990010),
                    Box::new(SpecExpression::Multiply(leaf(990011), leaf(990012))),
                ),
            ] {
                assert_eq!(evaluate(&expression, false), evaluate(&expression, true));
            }
            let maximum = if format == MachineIntegerType::Int32 {
                MachineTerm::constant(i32::MAX as u32)
            } else {
                MachineTerm::int64_constant(i64::MAX)
            };
            let one = if format == MachineIntegerType::Int32 {
                MachineTerm::constant(1)
            } else {
                MachineTerm::int64_constant(1)
            };
            let zero = if format == MachineIntegerType::Int32 {
                MachineTerm::constant(0)
            } else {
                MachineTerm::int64_constant(0)
            };
            let expression = SpecExpression::Multiply(
                Box::new(SpecExpression::Add(
                    Box::new(SpecExpression::Value(wrap(format, maximum))),
                    Box::new(SpecExpression::Value(wrap(format, one))),
                )),
                Box::new(SpecExpression::Value(wrap(format, zero))),
            );
            let paths = evaluate(&expression, false);
            assert_eq!(paths, evaluate(&expression, true));
            assert!(
                !paths[0].obligations.is_empty(),
                "zero result must retain inner overflow debt"
            );
        }
    }

    #[test]
    fn nested_signed_arithmetic_retains_opaque_machine_leaves() {
        // The old evaluator observes a whole native composite; the shared
        // producer observes a DAG containing retained opaque leaves. Compare
        // their exact arithmetic payloads, not those different bridge IDs.
        fn same_integer(left: &IntegerTerm, right: &IntegerTerm) {
            match (left, right) {
                (IntegerTerm::Machine(a), IntegerTerm::Machine(b)) => {
                    assert_eq!(a.ty(), b.ty());
                    assert_eq!(a.structural_value(), b.structural_value());
                }
                (IntegerTerm::Add(a, b), IntegerTerm::Add(c, d))
                | (IntegerTerm::Multiply(a, b), IntegerTerm::Multiply(c, d)) => {
                    same_integer(a, c);
                    same_integer(b, d);
                }
                _ => assert_eq!(left, right),
            }
        }
        fn same_domain(left: &Proposition, right: &Proposition) {
            match (left, right) {
                (Proposition::And(a, b), Proposition::And(c, d)) => {
                    same_domain(a, c);
                    same_domain(b, d);
                }
                (Proposition::ConditionIs(a, av), Proposition::ConditionIs(b, bv)) => {
                    assert_eq!(av, bv);
                    match (a, b) {
                        (
                            ConditionTerm::IntegerLessEqual(a, b),
                            ConditionTerm::IntegerLessEqual(c, d),
                        )
                        | (
                            ConditionTerm::IntegerGreaterEqual(a, b),
                            ConditionTerm::IntegerGreaterEqual(c, d),
                        ) => {
                            same_integer(a, c);
                            same_integer(b, d);
                        }
                        _ => assert_eq!(a, b),
                    }
                }
                _ => assert_eq!(left, right),
            }
        }
        for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let opaque = MachineTerm::BoolCast {
                to: format,
                value: Box::new(ConditionTerm::signed_less_than(
                    MachineTerm::Variable(Variable(990020)),
                    MachineTerm::constant(0),
                )),
            };
            let leaf = || Box::new(SpecExpression::Value(wrap(format, opaque.clone())));
            let expression =
                SpecExpression::Multiply(Box::new(SpecExpression::Add(leaf(), leaf())), leaf());
            let exports = KernelTermExport::machine_export_count();
            let mut execution = ExecutionBudget::new();
            let prepared = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                .unwrap()
                .unwrap();
            assert_eq!(prepared.obligations.len(), 2);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let shared = evaluate(&expression, false);
            let legacy = evaluate(&expression, true);
            assert_eq!(shared.len(), legacy.len());
            assert_eq!(shared[0].value, legacy[0].value);
            assert_eq!(shared[0].facts, legacy[0].facts);
            assert_eq!(shared[0].obligations.len(), legacy[0].obligations.len());
            for (a, b) in shared[0].obligations.iter().zip(&legacy[0].obligations) {
                same_domain(a.proposition(), b.proposition());
                assert_eq!(a.evaluation_domain, b.evaluation_domain);
                assert_eq!(a.assumable, b.assumable);
            }
        }
    }

    #[test]
    fn shared_signed_domains_retain_held_resource_metadata() {
        let operand = || {
            Box::new(SpecExpression::Value(CValue::Int32(MachineTerm::Variable(
                Variable(990005),
            ))))
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
                MachineTerm::constant(1)
            } else {
                MachineTerm::uint64_constant(1)
            };
            let maximum = if format == MachineIntegerType::UInt32 {
                MachineTerm::constant(u32::MAX)
            } else {
                MachineTerm::uint64_constant(u64::MAX)
            };
            for left in [MachineTerm::Variable(Variable(990001)), maximum] {
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
            Box::new(SpecExpression::Value(CValue::Int32(MachineTerm::Variable(
                Variable(990002),
            ))))
        };
        let unsigned = || {
            Box::new(SpecExpression::Value(CValue::UInt64(
                MachineTerm::Variable(Variable(990003)),
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
                MachineTerm::uint64_constant(0),
            )))
        };
        // A zero factor does not erase an inner shift's count domain. (A
        // quotient by zero would owe nothing: specification `/` is total.)
        let nested = SpecExpression::Multiply(
            zero(),
            Box::new(SpecExpression::ShiftLeft(unsigned(), unsigned())),
        );
        let paths = evaluate(&nested, false);
        assert_eq!(paths, evaluate(&nested, true));
        assert!(!paths[0].obligations.is_empty());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/shared_machine.rs");
}
