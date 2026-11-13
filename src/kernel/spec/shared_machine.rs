//! Shared arithmetic producers, with definedness kept outside the term.
//! Complete same-format arithmetic trees retain their operands in obligations.
//! Deferred paths use the same constructor after evaluating both operands.
//! Mixed-format and other unmigrated operations keep explicit native boundaries.
use super::*;
mod casts;
pub(super) use casts::cast_signedness;

pub(super) struct PreparedExpression {
    pub(super) value: KernelTerm,
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn operator(expression: &SpecExpression) -> Option<MachineBinaryOp> {
    Some(match expression {
        SpecExpression::Add(..) => MachineBinaryOp::Add,
        SpecExpression::Subtract(..) => MachineBinaryOp::Subtract,
        SpecExpression::Multiply(..) => MachineBinaryOp::Multiply,
        SpecExpression::Divide(..) => MachineBinaryOp::Divide,
        SpecExpression::Remainder(..) => MachineBinaryOp::Remainder,
        SpecExpression::ShiftLeft(..) => MachineBinaryOp::ShiftLeft,
        SpecExpression::ShiftRight(..) => MachineBinaryOp::ShiftRight,
        _ => return None,
    })
}

/// Retain evaluated scalar operands when the native operator has the same
/// format on both sides. Other promotion rules stay at the native boundary.
pub(super) fn apply_values(
    operator: Option<MachineBinaryOp>,
    left: &SpecValue,
    right: &SpecValue,
    budget: &SpecEvaluation<'_>,
) -> Option<PreparedExpression> {
    if budget.machine_result_production_disabled {
        return None;
    }
    let operator = operator?;
    let (a, left) = left.machine()?;
    let (b, right) = right.machine()?;
    if a != b
        || !matches!(
            a,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        )
    {
        return None;
    }
    let left = retained_operand(a, left);
    let right = retained_operand(b, right);
    Some(apply(a, operator, left, right, budget))
}

fn retained_operand(format: MachineIntegerType, value: MachineOperandView<'_>) -> KernelTerm {
    match value {
        MachineOperandView::Shared(value) => value.with_machine_observation_type(format),
        MachineOperandView::Legacy(value) => {
            // Native 32-bit operators read the low word and use the result
            // format's literal spelling. Normalize at this input boundary,
            // never by exporting a previously produced shared prefix.
            let value = if format.format().bits() == 32 {
                MachineTerm::operand32(format, value.clone())
            } else {
                value.clone()
            };
            KernelTerm::retained_native_machine_operand(format, &value)
        }
    }
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
                    | SpecExpression::Multiply(a, b)
                    | SpecExpression::Divide(a, b)
                    | SpecExpression::Remainder(a, b)
                    | SpecExpression::ShiftLeft(a, b)
                    | SpecExpression::ShiftRight(a, b) => {
                        let op = match expression {
                            SpecExpression::Add(..) => MachineBinaryOp::Add,
                            SpecExpression::Subtract(..) => MachineBinaryOp::Subtract,
                            SpecExpression::Multiply(..) => MachineBinaryOp::Multiply,
                            SpecExpression::Divide(..) => MachineBinaryOp::Divide,
                            SpecExpression::Remainder(..) => MachineBinaryOp::Remainder,
                            SpecExpression::ShiftLeft(..) => MachineBinaryOp::ShiftLeft,
                            _ => MachineBinaryOp::ShiftRight,
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
    for step in prepared {
        budget.consume_expression_step()?;
        match step {
            Prepared::Value(format, value) => {
                values.push(retained_operand(format, MachineOperandView::Legacy(value)));
            }
            Prepared::Binary(format, op) => {
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                let result = apply(format, op, left, right, budget);
                obligations.extend(result.obligations);
                values.push(result.value);
            }
        }
    }
    Ok(values
        .pop()
        .map(|value| PreparedExpression { value, obligations }))
}

/// Construct one result and its domain from already evaluated operands. Both
/// eager preparation and deferred path evaluation use this operation.
pub(super) fn apply(
    format: MachineIntegerType,
    op: MachineBinaryOp,
    left: KernelTerm,
    right: KernelTerm,
    budget: &SpecEvaluation<'_>,
) -> PreparedExpression {
    let mut obligations = Vec::new();
    let mut importer = KernelTermImport::default();
    let left_view = MachineOperandView::Shared(&left);
    let right_view = MachineOperandView::Shared(&right);
    let mut domain = Vec::new();
    let shift = matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight);
    if shift {
        let constant = |n: u64| {
            crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
        };
        let compare = |value, relation, n| {
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                relation,
                [value, MachineOperandView::Legacy(&constant(n))],
            )
        };
        let mut require_false = |condition| {
            if PureFactContext::decide_intrinsically(&condition) != Some(false) {
                domain.push(Proposition::ConditionIs(condition, false));
            }
        };
        if format.format().is_signed() {
            require_false(compare(right_view, CompareRelation::LessThan, 0));
        }
        require_false(compare(
            right_view,
            CompareRelation::GreaterEqual,
            u64::from(format.format().bits()),
        ));
        if op == MachineBinaryOp::ShiftLeft && format.format().is_signed() {
            require_false(compare(left_view, CompareRelation::LessThan, 0));
            domain.push(Proposition::ConditionIs(
                ConditionTerm::signed_shift_result_fits_views(format, left_view, right_view),
                true,
            ));
        }
    } else if matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::Remainder) {
        if SpecDivision::of(budget) == SpecDivision::CDefined {
            let zero =
                crate::kernel::machine_integer::range::constant_word(format, &0.into()).unwrap();
            domain.push(Proposition::ConditionIs(
                crate::kernel::machine_integer::comparison::condition_for_operand_views(
                    format,
                    CompareRelation::Equal,
                    [right_view, MachineOperandView::Legacy(&zero)],
                ),
                false,
            ));
        }
        if format.format().is_signed() {
            domain.push(Proposition::signed_division_exclusion_views(
                format, left_view, right_view,
            ));
        }
    } else if format.format().is_signed() {
        domain.push(Proposition::signed_arithmetic_domain_views(
            format, op, left_view, right_view,
        ));
    }
    if let Some(domain) = Proposition::arithmetic_domain(domain) {
        obligations.push(
            ProofObligation::evaluation_domain(domain).with_context(if shift {
                "shift expression is defined"
            } else {
                "arithmetic expression is defined"
            }),
        );
    }
    // Preserve the existing evaluator's literal-only folding.
    // Shared node construction itself is always structural.
    let term = if let (KernelTermNode::MachineLiteral(a), KernelTermNode::MachineLiteral(b)) =
        (left.node(), right.node())
    {
        let a = a.legacy_term();
        let b = b.legacy_term();
        let value = MachineTerm::logical_machine_binary(format, op, a, b);
        let value = wrap(format, value);
        importer.argument(&PureFunctionArgument::Value(value))
    } else {
        KernelTerm::machine_binary_shared(format, op, [left, right])
    };
    PreparedExpression {
        value: term,
        obligations,
    }
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

    fn boxed_domain(value: &Proposition) -> Proposition {
        match value {
            Proposition::And(a, b) => Proposition::And(Box::new(boxed_domain(a)), Box::new(boxed_domain(b))),
            Proposition::ConditionIs(condition, truth) => {
                crate::kernel::machine_integer::comparison::structural_native_comparison_of_integer_observation(condition, *truth)
                    .map(|(condition, truth)| Proposition::ConditionIs(condition, truth))
                    .unwrap_or_else(|| value.clone())
            }
            _ => value.clone(),
        }
    }

    fn native_results(paths: Vec<SpecExpressionPath>) -> Vec<SpecExpressionPath> {
        paths
            .into_iter()
            .map(|mut path| {
                path.value = path.value.into_native().into();
                path
            })
            .collect()
    }

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
        budget.machine_result_production_disabled = legacy;
        native_results(
            evaluate_spec_expression_paths_with_algebraic_bindings_in(
                SpecScope::unbound(&CState::new(), None),
                expression,
                assumptions,
                &mut budget,
            )
            .unwrap(),
        )
    }

    #[test]
    fn nested_division_retains_total_and_c_defined_domains() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let constant = |n: i64| {
                crate::kernel::machine_integer::range::constant_word(format, &n.into())
                    .unwrap_or_else(|| {
                        if format.format().bits() == 32 {
                            MachineTerm::constant(n as u32)
                        } else {
                            MachineTerm::uint64_constant(n as u64)
                        }
                    })
            };
            let min = if format.format().bits() == 32 {
                i32::MIN as i64
            } else {
                i64::MIN
            };
            for (a, b) in [
                (MachineTerm::Variable(Variable(991901)), constant(2)),
                (constant(min), constant(-1)),
                (constant(3), constant(0)),
            ] {
                for remainder in [false, true] {
                    let a = Box::new(SpecExpression::Value(wrap(format, a.clone())));
                    let b = Box::new(SpecExpression::Value(wrap(format, b.clone())));
                    let inner = if remainder {
                        SpecExpression::Remainder(a, b)
                    } else {
                        SpecExpression::Divide(a, b)
                    };
                    let expression = SpecExpression::Multiply(
                        Box::new(inner),
                        Box::new(SpecExpression::Value(wrap(format, constant(0)))),
                    );
                    for defined in [false, true] {
                        let run = |disabled| {
                            let mut execution = ExecutionBudget::new();
                            let mut budget = SpecEvaluation::logical(&mut execution);
                            budget.c_definedness = defined;
                            budget.machine_preparation_disabled = disabled;
                            budget.machine_result_production_disabled = disabled;
                            native_results(
                                evaluate_spec_expression_paths_with_algebraic_bindings_in(
                                    SpecScope::unbound(&CState::new(), None),
                                    &expression,
                                    &PureFactContext::new(),
                                    &mut budget,
                                )
                                .unwrap(),
                            )
                        };
                        assert_eq!(
                            run(false),
                            run(true),
                            "{format:?}, remainder={remainder}, defined={defined}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn shared_shifts_preserve_count_and_result_obligations() {
        // Storage differs deliberately: the shared result-bound comparison
        // keeps its operands, while the old producer emits a boxed Compare.
        // Export only in this parity oracle and compare the exact native trees.
        let native_paths = |mut paths: Vec<SpecExpressionPath>| {
            for path in &mut paths {
                for obligation in &mut path.obligations {
                    obligation.proposition = boxed_domain(obligation.proposition());
                }
            }
            paths
        };

        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let constant = |n: u64| {
                crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
            };
            for shift_right in [false, true] {
                for (left, count) in [
                    (constant(1), constant(0)),
                    (constant(1), constant(1)),
                    (constant(1), constant(u64::from(format.format().bits()))),
                    (MachineTerm::Variable(Variable(991902)), constant(1)),
                    (constant(1), MachineTerm::Variable(Variable(991903))),
                    (
                        MachineTerm::Variable(Variable(991902)),
                        MachineTerm::Variable(Variable(991903)),
                    ),
                ] {
                    let left = Box::new(SpecExpression::Value(wrap(format, left)));
                    let right = Box::new(SpecExpression::Value(wrap(format, count)));
                    let expression = if shift_right {
                        SpecExpression::ShiftRight(left, right)
                    } else {
                        SpecExpression::ShiftLeft(left, right)
                    };
                    assert_eq!(
                        native_paths(evaluate(&expression, false)),
                        native_paths(evaluate(&expression, true)),
                        "{format:?}, {expression:?}"
                    );
                }
            }
        }
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
    fn result_observations_preserve_opaque_native_identity() {
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let leaf = MachineTerm::opaque_conversion(
                "result_identity",
                MachineTerm::Variable(Variable(992220)),
            );
            let expression = SpecExpression::Subtract(
                Box::new(SpecExpression::Value(wrap(format, leaf))),
                Box::new(SpecExpression::Value(wrap(
                    format,
                    crate::kernel::machine_integer::range::constant_word(format, &1.into())
                        .unwrap(),
                ))),
            );
            let mut execution = ExecutionBudget::new();
            let prepared = prepare(&expression, &mut SpecEvaluation::logical(&mut execution))
                .unwrap()
                .unwrap();
            assert!(prepared.value.has_opaque_observation_boundary());
            let result = SpecValue::Shared(prepared.value);
            let legacy = evaluate(&expression, true).remove(0).value;
            assert_eq!(result.observe(), legacy.observe());
        }
    }

    #[test]
    fn opaque_observation_identity_survives_source_drop_and_distinguishes_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        let make = |id| {
            let format = MachineIntegerType::UInt64;
            let leaf = MachineTerm::opaque_conversion(
                "observation_owner",
                MachineTerm::Variable(Variable(id)),
            );
            SpecValue::Shared(KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Subtract,
                [
                    KernelTerm::retained_native_machine_operand(format, &leaf),
                    KernelTerm::retained_native_machine_operand(
                        format,
                        &MachineTerm::uint64_constant(1),
                    ),
                ],
            ))
        };
        let exports = KernelTermExport::machine_export_count();
        let observation = make(992250).observe().unwrap();
        assert_eq!(Some(observation.clone()), make(992250).observe());
        assert_ne!(Some(observation), make(992251).observe());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn deferred_requirements_preserve_results_domains_and_order() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let operand = |id| {
                Box::new(SpecExpression::Requires {
                    requirement: Box::new(SpecProposition::Comparison {
                        left: SpecExpression::Value(wrap(
                            format,
                            MachineTerm::Variable(Variable(id)),
                        )),
                        operator: CComparisonOperator::NotEqual,
                        right: SpecExpression::Value(wrap(
                            format,
                            crate::kernel::machine_integer::range::constant_word(format, &0.into())
                                .unwrap(),
                        )),
                    }),
                    value: Box::new(SpecExpression::Value(wrap(
                        format,
                        MachineTerm::Variable(Variable(id)),
                    ))),
                })
            };
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
            ] {
                let a = operand(992210);
                let b = operand(992211);
                let expression = match op {
                    MachineBinaryOp::Add => SpecExpression::Add(a, b),
                    MachineBinaryOp::Subtract => SpecExpression::Subtract(a, b),
                    MachineBinaryOp::Multiply => SpecExpression::Multiply(a, b),
                    MachineBinaryOp::Divide => SpecExpression::Divide(a, b),
                    MachineBinaryOp::Remainder => SpecExpression::Remainder(a, b),
                    MachineBinaryOp::ShiftLeft => SpecExpression::ShiftLeft(a, b),
                    MachineBinaryOp::ShiftRight => SpecExpression::ShiftRight(a, b),
                    _ => unreachable!(),
                };
                for held in [false, true] {
                    let assumptions = if held {
                        PureFactContext::new().assume_held_resource_domains()
                    } else {
                        PureFactContext::new()
                    };
                    let mut execution = ExecutionBudget::new();
                    let exports = KernelTermExport::machine_export_count();
                    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                        SpecScope::unbound(&CState::new(), None),
                        &expression,
                        &assumptions,
                        &mut SpecEvaluation::logical(&mut execution),
                    )
                    .unwrap();
                    assert_eq!(paths.len(), 1);
                    assert!(matches!(paths[0].value, SpecValue::Shared(_)));
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    let legacy = evaluate_with_assumptions(&expression, true, &assumptions);
                    let mut paths = native_results(paths);
                    let mut legacy = legacy;
                    for path in paths.iter_mut().chain(&mut legacy) {
                        for obligation in &mut path.obligations {
                            obligation.proposition = boxed_domain(obligation.proposition());
                        }
                    }
                    assert_eq!(paths, legacy, "{format:?} {op:?}, held={held}");
                    assert!(paths[0].obligations.len() >= 2);
                    for (a, b) in paths[0].obligations.iter().zip(&legacy[0].obligations) {
                        assert_eq!(a.evaluation_domain, b.evaluation_domain);
                        assert_eq!(a.assumable, b.assumable);
                    }
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
