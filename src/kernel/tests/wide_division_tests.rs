use super::*;
use num_bigint::BigInt;

const LEFT: Variable = Variable(155_001);
const RIGHT: Variable = Variable(155_002);

fn operation(a: CExpression, b: CExpression, remainder: bool) -> CExpression {
    if remainder {
        c_remainder(a, b)
    } else {
        c_divide(a, b)
    }
}

fn evaluated(expression: CExpression) -> CExpressionOutcome {
    let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

fn value(ty: MachineIntegerType, variable: Variable) -> CValue {
    match ty {
        MachineIntegerType::Int128 => CValue::Int128(Bitvector32Term::Variable(variable)),
        MachineIntegerType::UInt128 => CValue::UInt128(Bitvector32Term::Variable(variable)),
        _ => unreachable!(),
    }
}

fn guards(ty: MachineIntegerType) -> (ConditionTerm, ConditionTerm, ConditionTerm, Proposition) {
    let a = IntegerTerm::from_machine(ty, Bitvector32Term::Variable(LEFT)).unwrap();
    let b = IntegerTerm::from_machine(ty, Bitvector32Term::Variable(RIGHT)).unwrap();
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
) -> Vec<CExpressionPath> {
    if remainder {
        crate::kernel::eval::apply_c_remainder(
            value(ty, LEFT),
            value(ty, RIGHT),
            vec![],
            vec![],
            assumptions,
        )
    } else {
        crate::kernel::eval::apply_c_divide(
            value(ty, LEFT),
            value(ty, RIGHT),
            vec![],
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
                    Some(CUndefinedBehavior::DivisionByZero)
                } else if a == i128::MIN && b == -1 {
                    Some(CUndefinedBehavior::SignedOverflow)
                } else {
                    None
                };
                if let Some(bad) = bad {
                    assert_eq!(
                        outcome,
                        CExpressionOutcome::UndefinedBehavior(bad),
                        "{a}, {b}, {remainder}"
                    );
                } else {
                    let expected = if remainder {
                        BigInt::from(a) % BigInt::from(b)
                    } else {
                        BigInt::from(a) / BigInt::from(b)
                    };
                    let CExpressionOutcome::Value(value) = outcome else {
                        panic!("{outcome:?}")
                    };
                    assert_eq!(value.c_type(), CType::Int128);
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
                        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero)
                    );
                } else {
                    let CExpressionOutcome::Value(value) = outcome else {
                        panic!("{outcome:?}")
                    };
                    assert_eq!(value.c_type(), CType::UInt128);
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
                .find(|p| matches!(p.outcome, CExpressionOutcome::Value(_)))
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
            let CExpressionOutcome::Value(ref value) = normal.outcome else {
                unreachable!()
            };
            let term = match value {
                CValue::Int128(t) | CValue::UInt128(t) => t,
                _ => unreachable!(),
            };
            let Bitvector32Term::IntegerToMachine {
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
                    .filter(|p| !matches!(p.outcome, CExpressionOutcome::Value(_)))
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
        assert!(matches!(normal[0].outcome, CExpressionOutcome::Value(_)));
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
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow)
        );
        let zero_context = none.clone().assume_condition(zero.clone(), true);
        assert_eq!(
            paths(ty, remainder, &zero_context)[0].outcome,
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero)
        );
    }
}

#[test]
fn wide_division_minimum_dividend_still_checks_minus_one_for_remainder() {
    for remainder in [false, true] {
        let expression = operation(
            c_int128_literal(i128::MIN),
            CExpression::Value(value(MachineIntegerType::Int128, RIGHT)),
            remainder,
        );
        let (zero, _, minus_one, _) = guards(MachineIntegerType::Int128);
        let assumptions = PureFactContext::new().assume_condition(zero, false);
        let output = evaluate_c_expression_paths(
            &CState::new(),
            &expression,
            &assumptions,
            &mut ExecutionBudget::for_c_expression(&expression),
        )
        .unwrap();
        assert_eq!(output.len(), 2);
        let normal = output
            .iter()
            .find(|p| matches!(p.outcome, CExpressionOutcome::Value(_)))
            .unwrap();
        assert!(
            normal
                .facts
                .iter()
                .any(|f| f.proposition() == &Proposition::ConditionIs(minus_one.clone(), false))
        );
        assert!(output.iter().any(|p| p.outcome
            == CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow)));
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
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            );
        }
        assert_eq!(
            evaluated(operation(
                c_int128_literal(-7),
                c_cast(c_int32_literal(3), CType::Int128),
                remainder
            )),
            CExpressionOutcome::Value(
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
                    CType::Int128
                ),
                c_int128_literal(1),
                remainder
            )),
            CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero)
        );
    }
}

#[test]
fn wide_division_unknown_guards_cannot_produce_an_unconditional_theorem() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            assert!(
                prove_c_expression_evaluation(
                    CState::new(),
                    operation(
                        CExpression::Value(value(ty, LEFT)),
                        CExpression::Value(value(ty, RIGHT)),
                        remainder
                    )
                )
                .is_none()
            );
        }
    }
}

#[test]
fn wide_division_guard_queries_do_not_scan_unrelated_ambient_facts() {
    for remainder in [false, true] {
        let (zero, _, _, safe) = guards(MachineIntegerType::Int128);
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut context = PureFactContext::new();
            for i in 0..size {
                context =
                    context.assume_condition(ConditionTerm::Variable(Variable(156_000 + i)), true);
            }
            context = context
                .assume_condition(zero.clone(), false)
                .assume_proposition(safe.clone());
            let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                paths(MachineIntegerType::Int128, remainder, &context)
            });
            assert_eq!(output.len(), 1);
            assert!(work < 4096, "{size}: {work}");
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
            "{samples:?}"
        );
    }
}

#[test]
fn wide_division_work_scales_with_explicit_operations() {
    for ty in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for remainder in [false, true] {
            let mut samples = Vec::new();
            for size in [2usize, 8, 32, 128] {
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        assert_eq!(
                            paths(ty, remainder, &PureFactContext::new()).len(),
                            if ty == MachineIntegerType::Int128 {
                                3
                            } else {
                                2
                            }
                        );
                    }
                });
                assert!(work <= 8192 * size, "{size}: {work}");
                samples.push(work);
            }
            for pair in samples.windows(2) {
                assert!(pair[1] <= 4 * pair[0] + 64, "{samples:?}");
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
                CType::Int128
            } else {
                CType::UInt128
            };
            let function = c_function(
                cty,
                "wide_division",
                vec![c_parameter("a", cty), c_parameter("b", cty)],
                c_return(operation(c_variable("a"), c_variable("b"), remainder)),
            );
            let state = CState::new().with_local("caller", int32(77));
            let arguments = vec![
                CExpression::Value(value(ty, LEFT)),
                CExpression::Value(value(ty, RIGHT)),
            ];
            let check = || {
                prove_checked_c_function_execution_with_environment(
                    state.clone(),
                    function.clone(),
                    arguments.clone(),
                    assumptions.clone(),
                    CExecutionEnvironment::new(),
                    CExecutionSemantics::EXECUTE_BODIES,
                    CFunctionContractExecutionMode::VerifyLoops,
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
                CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                CFunctionContractExecutionMode::VerifyLoops,
            );
            assert!(first.agrees_with(&unsafe_entry).is_err());
        }
    }
}
