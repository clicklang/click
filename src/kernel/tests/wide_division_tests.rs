use super::*;
use num_bigint::BigInt;

const LEFT: Variable = Variable(155_001);
const RIGHT: Variable = Variable(155_002);

fn operation(a: ProgramExpression, b: ProgramExpression, remainder: bool) -> ProgramExpression {
    if remainder {
        c_remainder(a, b)
    } else {
        c_divide(a, b)
    }
}

fn evaluated(expression: ProgramExpression) -> ExpressionOutcome {
    let theorem = prove_c_expression_evaluation(ExecutionState::new(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

fn value(ty: MachineIntegerType, variable: Variable) -> ProgramValue {
    match ty {
        MachineIntegerType::Int128 => ProgramValue::Int128(MachineTerm::Variable(variable)),
        MachineIntegerType::UInt128 => ProgramValue::UInt128(MachineTerm::Variable(variable)),
        _ => unreachable!(),
    }
}

fn guards(ty: MachineIntegerType) -> (ConditionTerm, ConditionTerm, ConditionTerm, Proposition) {
    let a = IntegerTerm::from_machine(ty, MachineTerm::Variable(LEFT)).unwrap();
    let b = IntegerTerm::from_machine(ty, MachineTerm::Variable(RIGHT)).unwrap();
    let zero = ConditionTerm::integer_equal(b.clone(), IntegerTerm::constant_i64(0));
    let min = ConditionTerm::integer_equal(a, IntegerTerm::constant(i128::MIN.into()));
    let minus_one = ConditionTerm::integer_equal(b, IntegerTerm::constant_i64(-1));
    let safe = Proposition::Or(
        Box::new(Proposition::ConditionIs(min.clone(), false)),
        Box::new(Proposition::ConditionIs(minus_one.clone(), false)),
    );
    (zero, min, minus_one, safe)
}

fn paths(
    ty: MachineIntegerType,
    remainder: bool,
    assumptions: &PureFactContext,
) -> Vec<ExpressionPath> {
    if remainder {
        crate::kernel::eval::apply_c_remainder(
            value(ty, LEFT),
            value(ty, RIGHT),
            vec![].into(),
            vec![],
            assumptions,
        )
    } else {
        crate::kernel::eval::apply_c_divide(
            value(ty, LEFT),
            value(ty, RIGHT),
            vec![].into(),
            vec![],
            assumptions,
        )
    }
}

#[test]
fn wide_division_signed_constants_match_exact_oracle_and_native_failures() {
    let samples = [
        i128::MIN,
        i128::MIN + 1,
        -(1i128 << 100) - 7,
        -7,
        -3,
        -1,
        0,
        1,
        3,
        7,
        (1i128 << 100) + 7,
        i128::MAX,
    ];
    for a in samples {
        for b in samples {
            for remainder in [false, true] {
                let outcome = evaluated(operation(
                    c_int128_literal(a),
                    c_int128_literal(b),
                    remainder,
                ));
                let bad = if b == 0 {
                    Some(UndefinedBehavior::DivisionByZero)
                } else if a == i128::MIN && b == -1 {
                    Some(UndefinedBehavior::SignedOverflow)
                } else {
                    None
                };
                if let Some(bad) = bad {
                    assert_eq!(
                        outcome,
                        ExpressionOutcome::UndefinedBehavior(bad),
                        "{a}, {b}, {remainder}"
                    );
                } else {
                    let expected = if remainder {
                        BigInt::from(a) % BigInt::from(b)
                    } else {
                        BigInt::from(a) / BigInt::from(b)
                    };
                    let ExpressionOutcome::Value(value) = outcome else {
                        panic!("{outcome:?}")
                    };
                    assert_eq!(value.c_type(), ProgramType::Int128);
                    assert_eq!(
                        MachineIntegerType::Int128
                            .constant_from_value(&value)
                            .unwrap()
                            .to_integer(),
                        expected
                    );
                }
            }
        }
    }
}

#[test]
fn wide_division_unsigned_preserves_high_bits_and_format() {
    for a in [0, 1, 7, 1u128 << 64, (1u128 << 127) + 7, u128::MAX] {
        for b in [0, 1, 3, 1u128 << 64, (1u128 << 127) + 1, u128::MAX] {
            for remainder in [false, true] {
                let outcome = evaluated(operation(
                    c_uint128_literal(a),
                    c_uint128_literal(b),
                    remainder,
                ));
                if b == 0 {
                    assert_eq!(
                        outcome,
                        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)
                    );
                } else {
                    let ExpressionOutcome::Value(value) = outcome else {
                        panic!("{outcome:?}")
                    };
                    assert_eq!(value.c_type(), ProgramType::UInt128);
                    assert_eq!(
                        MachineIntegerType::UInt128
                            .constant_from_value(&value)
                            .unwrap()
                            .to_integer(),
                        BigInt::from(if remainder { a % b } else { a / b })
                    );
                }
            }
        }
    }
}

#[test]
fn wide_division_symbolic_paths_keep_native_guards_and_certified_observation() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            let (zero, _, _, safe) = guards(ty);
            let output = paths(ty, remainder, &PureFactContext::new());
            assert_eq!(
                output.len(),
                if ty == MachineIntegerType::Int128 {
                    3
                } else {
                    2
                }
            );
            let normal = output
                .iter()
                .find(|p| matches!(p.outcome, ExpressionOutcome::Value(_)))
                .unwrap();
            assert!(
                normal
                    .facts
                    .iter()
                    .any(|f| f.proposition() == &Proposition::ConditionIs(zero.clone(), false))
            );
            if ty == MachineIntegerType::Int128 {
                assert!(normal.facts.iter().any(|f| f.proposition() == &safe));
            }
            let ExpressionOutcome::Value(ref value) = normal.outcome else {
                unreachable!()
            };
            let term = match value {
                ProgramValue::Int128(t) | ProgramValue::UInt128(t) => t,
                _ => unreachable!(),
            };
            let MachineTerm::IntegerToMachine {
                value: result,
                destination,
            } = term
            else {
                unreachable!()
            };
            assert_eq!(*destination, ty);
            assert!(matches!(
                (remainder, result.as_ref()),
                (false, IntegerTerm::TruncatingQuotient(_, _))
                    | (true, IntegerTerm::TruncatingRemainder(_, _))
            ));
            let equation = Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    IntegerTerm::from_machine(ty, term.clone()).unwrap(),
                    result.as_ref().clone(),
                ),
                true,
            );
            assert!(
                normal
                    .facts
                    .iter()
                    .any(|f| f.proposition() == &equation && f.is_certified())
            );
            assert!(
                output
                    .iter()
                    .filter(|p| !matches!(p.outcome, ExpressionOutcome::Value(_)))
                    .all(|p| !p.facts.iter().any(|f| f.is_certified()))
            );
        }
    }
}

#[test]
fn wide_division_each_missing_guard_retains_its_undefined_path() {
    let ty = MachineIntegerType::Int128;
    let (zero, min, minus_one, safe) = guards(ty);
    for remainder in [false, true] {
        let none = PureFactContext::new();
        let nonzero = none.clone().assume_condition(zero.clone(), false);
        let safe_only = none.clone().assume_proposition(safe.clone());
        let both = nonzero.clone().assume_proposition(safe.clone());
        assert_eq!(paths(ty, remainder, &none).len(), 3);
        assert_eq!(paths(ty, remainder, &nonzero).len(), 2);
        assert_eq!(paths(ty, remainder, &safe_only).len(), 2);
        let normal = paths(ty, remainder, &both);
        assert_eq!(normal.len(), 1);
        assert!(matches!(normal[0].outcome, ExpressionOutcome::Value(_)));
        for condition in [min.clone(), minus_one.clone()] {
            let sufficient = nonzero.clone().assume_condition(condition, false);
            assert_eq!(paths(ty, remainder, &sufficient).len(), 1);
        }
        let overflow = nonzero
            .clone()
            .assume_condition(min.clone(), true)
            .assume_condition(minus_one.clone(), true);
        assert_eq!(
            paths(ty, remainder, &overflow)[0].outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)
        );
        let zero_context = none.clone().assume_condition(zero.clone(), true);
        assert_eq!(
            paths(ty, remainder, &zero_context)[0].outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)
        );
    }
}

#[test]
fn wide_division_minimum_dividend_still_checks_minus_one_for_remainder() {
    for remainder in [false, true] {
        let expression = operation(
            c_int128_literal(i128::MIN),
            ProgramExpression::Value(value(MachineIntegerType::Int128, RIGHT)),
            remainder,
        );
        let (zero, _, minus_one, _) = guards(MachineIntegerType::Int128);
        let assumptions = PureFactContext::new().assume_condition(zero, false);
        let output = evaluate_c_expression_paths(
            &ExecutionState::new(),
            &expression,
            &assumptions,
            &mut ExecutionBudget::for_c_expression(&expression),
        )
        .unwrap();
        assert_eq!(output.len(), 2);
        let normal = output
            .iter()
            .find(|p| matches!(p.outcome, ExpressionOutcome::Value(_)))
            .unwrap();
        assert!(
            normal
                .facts
                .iter()
                .any(|f| f.proposition() == &Proposition::ConditionIs(minus_one.clone(), false))
        );
        assert!(output.iter().any(|p| p.outcome
            == ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)));
    }
}

#[test]
fn wide_division_promotions_are_explicit_and_operand_definedness_is_preserved() {
    for remainder in [false, true] {
        for pair in [
            (c_int128_literal(7), c_uint128_literal(3)),
            (c_int128_literal(7), c_int32_literal(3)),
            (c_int64_literal(7), c_uint128_literal(3)),
            (c_uint128_literal(7), c_void_value()),
        ] {
            assert_eq!(
                evaluated(operation(pair.0, pair.1, remainder)),
                ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
            );
        }
        assert_eq!(
            evaluated(operation(
                c_int128_literal(-7),
                c_cast(c_int32_literal(3), ProgramType::Int128),
                remainder
            )),
            ExpressionOutcome::Value(
                MachineIntegerType::Int128
                    .constant_value(
                        MachineIntegerConstant::from_signed(
                            MachineIntegerType::Int128.format(),
                            if remainder { -1 } else { -2 }
                        )
                        .unwrap()
                    )
                    .unwrap()
            )
        );
        assert_eq!(
            evaluated(operation(
                c_cast(
                    c_divide(c_int64_literal(1), c_int64_literal(0)),
                    ProgramType::Int128
                ),
                c_int128_literal(1),
                remainder
            )),
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)
        );
    }
}

#[test]
fn wide_division_unknown_guards_cannot_produce_an_unconditional_theorem() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            assert!(
                prove_c_expression_evaluation(
                    ExecutionState::new(),
                    operation(
                        ProgramExpression::Value(value(ty, LEFT)),
                        ProgramExpression::Value(value(ty, RIGHT)),
                        remainder
                    )
                )
                .is_none()
            );
        }
    }
}

fn inequality_guards(ty: MachineIntegerType) -> (ConditionTerm, Proposition) {
    let a = IntegerTerm::from_machine(ty, MachineTerm::Variable(LEFT)).unwrap();
    let b = IntegerTerm::from_machine(ty, MachineTerm::Variable(RIGHT)).unwrap();
    let nonzero = ConditionTerm::integer_not_equal(b.clone(), IntegerTerm::constant_i64(0));
    let safe = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::integer_not_equal(a, IntegerTerm::constant(i128::MIN.into())),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::integer_not_equal(b, IntegerTerm::constant_i64(-1)),
            true,
        )),
    );
    (nonzero, safe)
}

#[test]
fn wide_division_accepts_inequality_guards_without_erasing_native_failures() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            let (nonzero, safe) = inequality_guards(ty);
            let zero = PureFactContext::new().assume_condition(nonzero.clone(), false);
            let output = paths(ty, remainder, &zero);
            assert_eq!(output.len(), 1);
            assert_eq!(
                output[0].outcome,
                ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)
            );
            let context = PureFactContext::new().assume_condition(nonzero, true);
            if ty == MachineIntegerType::Int128 {
                assert!(
                    paths(ty, remainder, &context)
                        .iter()
                        .any(|path| path.outcome
                            == ExpressionOutcome::UndefinedBehavior(
                                UndefinedBehavior::SignedOverflow
                            ))
                );
                let Proposition::Or(a, b) = safe.clone() else {
                    unreachable!()
                };
                for guard in [safe, *a.clone(), *b.clone()] {
                    let output = paths(ty, remainder, &context.clone().assume_proposition(guard));
                    assert_eq!(output.len(), 1);
                    assert!(matches!(output[0].outcome, ExpressionOutcome::Value(_)));
                }
                let context = [*a, *b].into_iter().fold(context, |context, guard| {
                    let Proposition::ConditionIs(condition, _) = guard else {
                        unreachable!()
                    };
                    context.assume_condition(condition, false)
                });
                assert_eq!(
                    paths(ty, remainder, &context)[0].outcome,
                    ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)
                );
            } else {
                assert_eq!(paths(ty, remainder, &context).len(), 1);
            }
        }
    }
}

#[test]
fn wide_division_full_disjunction_survives_known_endpoint_simplification() {
    for remainder in [false, true] {
        let (zero, min, minus_one, equality_safe) = guards(MachineIntegerType::Int128);
        let (_, inequality_safe) = inequality_guards(MachineIntegerType::Int128);
        for safe in [equality_safe, inequality_safe] {
            for known in [min.clone(), minus_one.clone()] {
                let context = PureFactContext::new()
                    .assume_condition(zero.clone(), false)
                    .assume_condition(known, true)
                    .assume_proposition(safe.clone());
                let output = paths(MachineIntegerType::Int128, remainder, &context);
                assert_eq!(output.len(), 1);
                assert!(matches!(output[0].outcome, ExpressionOutcome::Value(_)));
            }
        }
    }
}

#[test]
fn wide_division_checked_function_artifacts_recheck_exactly() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            let (zero, _, _, safe) = guards(ty);
            let mut assumptions = PureFactContext::new().assume_condition(zero, false);
            if ty == MachineIntegerType::Int128 {
                assumptions = assumptions.assume_proposition(safe);
            }
            let cty = if ty == MachineIntegerType::Int128 {
                ProgramType::Int128
            } else {
                ProgramType::UInt128
            };
            let function = c_function(
                cty,
                "wide_division",
                vec![c_parameter("a", cty), c_parameter("b", cty)],
                c_return(operation(c_variable("a"), c_variable("b"), remainder)),
            );
            let state = ExecutionState::new().with_local("caller", int32(77));
            let arguments = vec![
                ProgramExpression::Value(value(ty, LEFT)),
                ProgramExpression::Value(value(ty, RIGHT)),
            ];
            let check = || {
                prove_checked_c_function_execution_with_environment(
                    state.clone(),
                    function.clone(),
                    arguments.clone(),
                    assumptions.clone(),
                    ExecutionEnvironment::new(),
                    ExecutionSemantics::EXECUTE_BODIES,
                    FunctionContractExecutionMode::VerifyLoops,
                )
            };
            let first = check();
            let recheck = check();
            assert_eq!(first.agrees_with(&recheck), Ok(()));
            assert_eq!(first.paths().len(), 1);
            assert!(
                first.paths()[0]
                    .facts()
                    .iter()
                    .any(ExecutionPureFact::is_certified)
            );
            // The same function without the guard assumptions retains its UB
            // paths, so its artifact cannot agree with the checked safe one.
            let unsafe_entry = prove_checked_c_function_execution_with_environment(
                state,
                function,
                arguments,
                PureFactContext::new(),
                ExecutionEnvironment::new(),
                ExecutionSemantics::EXECUTE_BODIES,
                FunctionContractExecutionMode::VerifyLoops,
            );
            assert!(first.agrees_with(&unsafe_entry).is_err());
        }
    }
}

fn promoted_division_expression(ty: MachineIntegerType, remainder: bool) -> ProgramExpression {
    let divisor = ProgramExpression::Cast {
        expression: Box::new(ProgramExpression::Value(ty.symbolic_value(RIGHT))),
        target_type: ProgramType::Int128,
        integer_mode: IntegerCastMode::CConversion,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    operation(
        ProgramExpression::Value(value(MachineIntegerType::Int128, LEFT)),
        divisor,
        remainder,
    )
}

fn native_divisor_equal(ty: MachineIntegerType, constant: i64) -> ConditionTerm {
    let divisor = MachineTerm::Variable(RIGHT);
    match ty {
        MachineIntegerType::Int32 => {
            ConditionTerm::equal(divisor, MachineTerm::constant(constant as i32 as u32))
        }
        MachineIntegerType::Int64 => {
            ConditionTerm::int64_equal(divisor, MachineTerm::int64_constant(constant))
        }
        _ => unreachable!(),
    }
}

fn promoted_division_safe_guard(ty: MachineIntegerType) -> Proposition {
    let dividend =
        IntegerTerm::from_machine(MachineIntegerType::Int128, MachineTerm::Variable(LEFT)).unwrap();
    Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::integer_not_equal(dividend, IntegerTerm::constant(i128::MIN.into())),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            native_divisor_equal(ty, -1),
            false,
        )),
    )
}

#[test]
fn wide_promoted_divisors_keep_native_guards_and_overflow_disjunctions() {
    for ty in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        for remainder in [false, true] {
            let expression = promoted_division_expression(ty, remainder);
            let evaluate = |context: &PureFactContext| {
                evaluate_c_expression_paths(
                    &ExecutionState::new(),
                    &expression,
                    context,
                    &mut ExecutionBudget::for_c_expression(&expression),
                )
                .unwrap()
            };
            let base = PureFactContext::new().defer_non_exact_condition_reasoning();
            let nonzero = base
                .clone()
                .assume_condition(native_divisor_equal(ty, 0), false);
            let safe = nonzero
                .clone()
                .assume_proposition(promoted_division_safe_guard(ty));
            let output = evaluate(&safe);
            assert_eq!(output.len(), 1);
            assert!(matches!(output[0].outcome, ExpressionOutcome::Value(_)));

            assert!(evaluate(&base).iter().any(|path| path.outcome
                == ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)));
            assert!(evaluate(&nonzero).iter().any(|path| path.outcome
                == ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)));
            let zero = base.assume_condition(native_divisor_equal(ty, 0), true);
            let output = evaluate(&zero);
            assert_eq!(output.len(), 1);
            assert_eq!(
                output[0].outcome,
                ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::DivisionByZero)
            );
            let dividend =
                IntegerTerm::from_machine(MachineIntegerType::Int128, MachineTerm::Variable(LEFT))
                    .unwrap();
            let overflow = nonzero
                .assume_condition(native_divisor_equal(ty, -1), true)
                .assume_condition(
                    ConditionTerm::integer_equal(dividend, IntegerTerm::constant(i128::MIN.into())),
                    true,
                );
            let output = evaluate(&overflow);
            assert_eq!(output.len(), 1);
            assert_eq!(
                output[0].outcome,
                ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow)
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/wide_division_tests.rs");
}
