//! Execution arithmetic retains produced operands across expression paths.
//! Native operators remain explicit boundaries for unmigrated operations and
//! pointer arithmetic; they retain their original metadata and definedness.
use super::*;
use crate::kernel::execution_value::ExecutionValue;
type ExecutionValuePath = CExpressionPath<ExecutionValue>;
use crate::kernel::MachineBinaryOp as Op;

#[derive(Clone, Copy)]
enum Binary {
    Machine(Op),
    Comparison(CComparisonOperator),
}

pub(in crate::kernel) fn evaluate_expression_value_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    if let CExpression::Conditional {
        condition,
        then_branch,
        else_branch,
    } = expression
    {
        budget.consume_expression_step()?;
        return conditional_paths(
            state,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        );
    }
    let (operation, left, right) = match expression {
        CExpression::Add(left, right) => (Binary::Machine(Op::Add), left, right),
        CExpression::Subtract(left, right) => (Binary::Machine(Op::Subtract), left, right),
        CExpression::Multiply(left, right) => (Binary::Machine(Op::Multiply), left, right),
        CExpression::Divide(left, right) => (Binary::Machine(Op::Divide), left, right),
        CExpression::BitwiseAnd(left, right) => (Binary::Machine(Op::BitwiseAnd), left, right),
        CExpression::BitwiseOr(left, right) => (Binary::Machine(Op::BitwiseOr), left, right),
        CExpression::BitwiseXor(left, right) => (Binary::Machine(Op::BitwiseXor), left, right),
        CExpression::LessThan(left, right) => (
            Binary::Comparison(CComparisonOperator::LessThan),
            left,
            right,
        ),
        CExpression::LessEqual(left, right) => (
            Binary::Comparison(CComparisonOperator::LessEqual),
            left,
            right,
        ),
        CExpression::GreaterThan(left, right) => (
            Binary::Comparison(CComparisonOperator::GreaterThan),
            left,
            right,
        ),
        CExpression::GreaterEqual(left, right) => (
            Binary::Comparison(CComparisonOperator::GreaterEqual),
            left,
            right,
        ),
        _ => {
            return Ok(super::expression::evaluate_native_expression_paths(
                state,
                expression,
                assumptions,
                budget,
            )?
            .into_iter()
            .map(Into::into)
            .collect());
        }
    };
    budget.consume_expression_step()?;
    let (left_step_width, right_step_width) = if matches!(
        operation,
        Binary::Machine(Op::Add | Op::Subtract) | Binary::Comparison(_)
    ) {
        (
            c_expression_pointer_step_width(state, left),
            c_expression_pointer_step_width(state, right),
        )
    } else {
        (None, None)
    };
    let mut paths = Vec::new();
    for mut left_path in evaluate_expression_value_paths(state, left, assumptions, budget)? {
        refuse_freed_pointer(state, &mut left_path, assumptions);
        let CExpressionOutcome::Value(left_value) = left_path.outcome else {
            paths.push(left_path);
            continue;
        };
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for mut right_path in
            evaluate_expression_value_paths(state, right, &right_assumptions, budget)?
        {
            // Match the native binary evaluator: pointer validity uses the
            // incoming context, while the right expression sees left debts.
            refuse_freed_pointer(state, &mut right_path, assumptions);
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let CExpressionOutcome::Value(right_value) = right_path.outcome else {
                paths.push(ExecutionValuePath {
                    facts,
                    obligations,
                    ..right_path
                });
                continue;
            };
            if let Binary::Comparison(operator) = operation {
                let native_paths = if let Some(condition) =
                    retained_comparison(operator, &left_value, &right_value)
                {
                    condition_as_c_int32_paths(condition, facts, obligations, assumptions)
                } else {
                    super::operators::apply_c_comparison(
                        state,
                        operator,
                        left_value.clone().into_native(),
                        right_value.into_native(),
                        left_step_width,
                        right_step_width,
                        facts,
                        obligations,
                        assumptions,
                    )
                };
                paths.extend(native_paths.into_iter().map(ExecutionValuePath::from));
                continue;
            }
            let Binary::Machine(op) = operation else {
                unreachable!()
            };
            if let Some(value) = retained_binary(op, &left_value, &right_value) {
                if op == Op::BitwiseAnd
                    && let ExecutionValue::Shared(root) = &value
                    && let Some(equation) =
                        crate::kernel::spec::bitwise_tag_equation(root, assumptions)
                {
                    facts.push(ExecutionPureFact::new(Proposition::ConditionIs(
                        equation, true,
                    )));
                }
                paths.push(ExecutionValuePath {
                    outcome: CExpressionOutcome::Value(value),
                    facts,
                    obligations,
                });
                continue;
            }
            // Full CValue payloads cross this boundary, including pointer
            // provenance and qualifications. No numeric projection is used.
            let left_value = left_value.clone().into_native();
            let right_value = right_value.into_native();
            let native = match op {
                Op::Add => apply_c_add(
                    state,
                    left_value,
                    right_value,
                    left_step_width,
                    right_step_width,
                    facts,
                    obligations,
                    assumptions,
                )
                .into_iter()
                .map(super::operators::fold_c_int32_constant_increment)
                .collect(),
                Op::Subtract => apply_c_subtract(
                    state,
                    left_value,
                    right_value,
                    left_step_width,
                    right_step_width,
                    facts,
                    obligations,
                    assumptions,
                ),
                Op::Multiply => {
                    apply_c_multiply(left_value, right_value, facts, obligations, assumptions)
                }
                Op::Divide => {
                    apply_c_divide(left_value, right_value, facts, obligations, assumptions)
                }
                Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor => apply_c_bitwise_binary(
                    left_value,
                    right_value,
                    facts,
                    obligations,
                    assumptions,
                    match op {
                        Op::BitwiseAnd => CBitwiseOperation::And,
                        Op::BitwiseOr => CBitwiseOperation::Or,
                        Op::BitwiseXor => CBitwiseOperation::Xor,
                        _ => unreachable!(),
                    },
                ),
                _ => unreachable!(),
            };
            paths.extend(native.into_iter().map(ExecutionValuePath::from));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn retained_comparison(
    operator: CComparisonOperator,
    left: &ExecutionValue,
    right: &ExecutionValue,
) -> Option<ConditionTerm> {
    let (format, left) = left.machine()?;
    let (right_format, right) = right.machine()?;
    if format != right_format
        || !matches!(
            format,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        )
    {
        return None;
    }
    let relation = match operator {
        CComparisonOperator::LessThan => CompareRelation::LessThan,
        CComparisonOperator::LessEqual => CompareRelation::LessEqual,
        CComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
        CComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
        _ => return None,
    };
    Some(
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            relation,
            [left, right],
        ),
    )
}

fn conditional_paths(
    state: &CState,
    condition: &CExpression,
    then_branch: &CExpression,
    else_branch: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_condition_paths(state, condition, assumptions, budget)? {
        let CExpressionOutcome::Value(value) = path.outcome else {
            paths.push(path.into());
            continue;
        };
        for truthiness in c_truthiness_paths(value, path.facts, path.obligations, assumptions) {
            let branch = if truthiness.is_true {
                then_branch
            } else {
                else_branch
            };
            let branch_assumptions = assumptions_with_path_context(
                assumptions,
                &truthiness.facts,
                &truthiness.obligations,
            );
            for path in evaluate_expression_value_paths(state, branch, &branch_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &truthiness.facts,
                    &truthiness.obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                paths.push(ExecutionValuePath {
                    facts,
                    obligations,
                    ..path
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn refuse_freed_pointer(
    state: &CState,
    path: &mut ExecutionValuePath,
    assumptions: &PureFactContext,
) {
    if let CExpressionOutcome::Value(ExecutionValue::Native(value)) = &path.outcome
        && let Some(undefined) = freed_pointer_use(state, value, assumptions)
    {
        path.outcome = CExpressionOutcome::UndefinedBehavior(undefined);
    }
}

fn retained_binary(
    op: Op,
    left: &ExecutionValue,
    right: &ExecutionValue,
) -> Option<ExecutionValue> {
    if !matches!(
        op,
        Op::Add | Op::Subtract | Op::Multiply | Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor
    ) {
        return None;
    }
    let (format, left) = left.machine()?;
    let (right_format, right) = right.machine()?;
    if format != right_format
        || !matches!(
            format,
            MachineIntegerType::UInt32 | MachineIntegerType::UInt64
        ) && !(matches!(op, Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor)
            && matches!(
                format,
                MachineIntegerType::Int32 | MachineIntegerType::Int64
            ))
    {
        return None;
    }
    let children = [
        KernelTerm::retained_machine_operand(format, left),
        KernelTerm::retained_machine_operand(format, right),
    ];
    let raw = KernelTerm::machine_binary_shared(format, op, children.clone());
    // These constructors reproduce MachineTerm's native root reductions, not
    // an equality/fact-driven choice of the result representation.
    let value =
        crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node(&raw, &children)?;
    Some(ExecutionValue::from(value))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn evaluate(expression: &CExpression) -> Vec<ExecutionValuePath> {
        evaluate_expression_value_paths(
            &CState::new(),
            expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
    }
    #[test]
    fn retained_execution_unsigned_operators_match_native_roots() {
        for format in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
            let wrap = |term| match format {
                MachineIntegerType::UInt32 => CValue::UInt32(term),
                MachineIntegerType::UInt64 => CValue::UInt64(term),
                _ => unreachable!(),
            };
            let constant = |n| {
                if format == MachineIntegerType::UInt32 {
                    MachineTerm::uint32_constant(n as u32)
                } else {
                    MachineTerm::uint64_constant(n)
                }
            };
            let variable = MachineTerm::Variable(Variable(991101));
            let terms = [
                constant(0),
                constant(1),
                constant(u64::MAX),
                variable.clone(),
                MachineTerm::machine_binary(format, Op::Add, variable.clone(), constant(2)),
                MachineTerm::machine_binary(format, Op::Subtract, variable.clone(), constant(2)),
            ];
            for op in [Op::Add, Op::Subtract, Op::Multiply] {
                for left in &terms {
                    for right in &terms {
                        let a = ExecutionValue::from(wrap(left.clone()));
                        let b = ExecutionValue::from(wrap(right.clone()));
                        let result = retained_binary(op, &a, &b).unwrap();
                        assert_eq!(
                            result.into_native(),
                            wrap(MachineTerm::machine_binary(
                                format,
                                op,
                                left.clone(),
                                right.clone()
                            )),
                            "{format:?} {op:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn retained_execution_conditional_keeps_selected_value_without_export() {
        let expression = CExpression::Conditional {
            condition: Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(1)))),
            then_branch: Box::new(CExpression::BitwiseXor(
                Box::new(CExpression::Value(CValue::UInt32(MachineTerm::Variable(
                    Variable(991103),
                )))),
                Box::new(CExpression::Value(CValue::UInt32(
                    MachineTerm::uint32_constant(7),
                ))),
            )),
            else_branch: Box::new(CExpression::Variable("not_evaluated".into())),
        };
        let exports = KernelTermExport::machine_export_count();
        let paths = evaluate(&expression);
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            paths[0].outcome,
            CExpressionOutcome::Value(ref value) if matches!(value, ExecutionValue::Shared(_))
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_execution_bitwise_formats_match_native() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let left = format.symbolic_value(Variable(991104));
            let right = format.symbolic_value(Variable(991105));
            for (op, operation) in [
                (Op::BitwiseAnd, CBitwiseOperation::And),
                (Op::BitwiseOr, CBitwiseOperation::Or),
                (Op::BitwiseXor, CBitwiseOperation::Xor),
            ] {
                let retained =
                    retained_binary(op, &left.clone().into(), &right.clone().into()).unwrap();
                let expected = apply_c_bitwise_binary(
                    left.clone(),
                    right.clone(),
                    ExecutionFacts::new(),
                    Vec::new(),
                    &PureFactContext::new(),
                    operation,
                );
                assert_eq!(
                    CExpressionOutcome::Value(retained.into_native()),
                    expected[0].outcome
                );
            }
        }
    }

    #[test]
    fn retained_execution_order_comparisons_match_native_paths() {
        for (left, right) in [(0, 1), (1, 0), (u32::MAX, 0), (7, 7)] {
            for (operator, expression) in [
                (
                    CComparisonOperator::LessThan,
                    CExpression::LessThan as fn(_, _) -> _,
                ),
                (CComparisonOperator::LessEqual, CExpression::LessEqual),
                (CComparisonOperator::GreaterThan, CExpression::GreaterThan),
                (CComparisonOperator::GreaterEqual, CExpression::GreaterEqual),
            ] {
                let left = CValue::UInt32(MachineTerm::uint32_constant(left));
                let right = CValue::UInt32(MachineTerm::uint32_constant(right));
                let result = evaluate(&expression(
                    Box::new(CExpression::Value(left.clone())),
                    Box::new(CExpression::Value(right.clone())),
                ));
                let expected = super::super::operators::apply_c_comparison(
                    &CState::new(),
                    operator,
                    left,
                    right,
                    None,
                    None,
                    ExecutionFacts::new(),
                    Vec::new(),
                    &PureFactContext::new(),
                );
                assert_eq!(
                    result
                        .into_iter()
                        .map(|path| path.map_value(ExecutionValue::into_native))
                        .collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn retained_execution_comparison_reads_shared_operands_without_export() {
        let format = MachineIntegerType::UInt32;
        let mut left = ExecutionValue::from(format.symbolic_value(Variable(991106)));
        for _ in 0..32 {
            left = retained_binary(
                Op::Multiply,
                &left,
                &ExecutionValue::from(CValue::UInt32(MachineTerm::uint32_constant(3))),
            )
            .unwrap();
        }
        let exports = KernelTermExport::machine_export_count();
        assert!(
            retained_comparison(
                CComparisonOperator::LessThan,
                &left,
                &ExecutionValue::from(CValue::UInt32(MachineTerm::uint32_constant(10)))
            )
            .is_some()
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_execution_preserves_signed_overflow_and_unbound_errors() {
        let overflow = CExpression::Add(
            Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(
                i32::MAX as u32,
            )))),
            Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(1)))),
        );
        assert!(
            evaluate(&overflow)
                .iter()
                .any(|path| matches!(path.outcome, CExpressionOutcome::UndefinedBehavior(_)))
        );
        let missing = CExpression::Multiply(
            Box::new(CExpression::Variable("missing".into())),
            Box::new(CExpression::Value(CValue::UInt32(
                MachineTerm::uint32_constant(2),
            ))),
        );
        assert!(matches!(&evaluate(&missing)[0].outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(name)) if name == "missing"));
        assert!(
            retained_binary(
                Op::Add,
                &CValue::Int32(MachineTerm::constant(1)).into(),
                &CValue::UInt32(MachineTerm::uint32_constant(1)).into()
            )
            .is_none()
        );
    }

    #[test]
    fn retained_bitwise_and_preserves_tag_facts_and_missing_bound_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let word = MachineTerm::Variable(Variable(998272));
        let tag = MachineTerm::Variable(Variable(998273));
        let lower = ConditionTerm::signed_less_equal(0u32.into(), tag.clone());
        let upper = ConditionTerm::signed_less_equal(tag.clone(), 1u32.into());
        let empty = PureFactContext::new();
        let nonnegative = empty.clone().assume_condition(lower, true);
        let bounded = nonnegative.clone().assume_condition(upper.clone(), true);
        let upper_only = empty.clone().assume_condition(upper, true);
        let left = CValue::UInt64(MachineTerm::uint64_bitwise_or(
            word.clone(),
            MachineTerm::uint64_from_int32(tag),
        ));
        let right = CValue::UInt64(MachineTerm::uint64_constant(!3));
        let added = CValue::UInt64(MachineTerm::uint64_add(
            word.clone(),
            MachineTerm::uint64_constant(1),
        ));
        let clear = empty.clone().assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_and(word, MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(0),
            ),
            true,
        );
        for (left, context, count) in [
            (left.clone(), &empty, 0),
            (left.clone(), &nonnegative, 0),
            (left.clone(), &upper_only, 0),
            (left, &bounded, 1),
            (added.clone(), &empty, 0),
            (added, &clear, 1),
        ] {
            let expression = CExpression::BitwiseAnd(
                Box::new(CExpression::Value(left.clone())),
                Box::new(CExpression::Value(right.clone())),
            );
            let expected = apply_c_bitwise_binary(
                left.clone(),
                right.clone(),
                ExecutionFacts::new(),
                Vec::new(),
                context,
                CBitwiseOperation::And,
            );
            let exports = KernelTermExport::machine_export_count();
            let actual = evaluate_expression_value_paths(
                &CState::new(),
                &expression,
                context,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(actual.len(), 1);
            assert_eq!(actual[0].facts.len(), count);
            assert_eq!(actual[0].facts.len(), expected[0].facts.len());
            assert_eq!(
                actual[0]
                    .outcome
                    .clone()
                    .map_value(ExecutionValue::into_native),
                expected[0].outcome
            );
            for (actual, expected) in actual[0].facts.iter().zip(expected[0].facts.iter()) {
                let actual =
                    crate::kernel::proof::proposition_identity_key(actual.proposition()).unwrap();
                let expected =
                    crate::kernel::proof::proposition_identity_key(expected.proposition()).unwrap();
                assert_eq!(actual, expected);
            }
        }
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/retained_expression/tests.rs");
    }
}
