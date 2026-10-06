use super::*;
use num_bigint::BigInt;

fn evaluated(expression: CExpression) -> CExpressionOutcome {
    let theorem = prove_c_expression_evaluation(CState::new(), expression).unwrap();
    let Proposition::CExpressionEvaluates { outcome, .. } = theorem.proposition() else {
        unreachable!()
    };
    outcome.clone()
}

fn product_and_bounds(
    left: MachineIntegerType,
    right: MachineIntegerType,
) -> (IntegerTerm, [ConditionTerm; 2]) {
    let product = IntegerTerm::multiply(
        IntegerTerm::from_machine(left, Bitvector32Term::Variable(Variable(150_001))).unwrap(),
        IntegerTerm::from_machine(right, Bitvector32Term::Variable(Variable(150_002))).unwrap(),
    );
    let (min, max) = MachineIntegerType::Int128.format().bounds();
    let bounds = [
        ConditionTerm::integer_greater_equal(product.clone(), IntegerTerm::constant(min)),
        ConditionTerm::integer_less_equal(product.clone(), IntegerTerm::constant(max)),
    ];
    (product, bounds)
}

#[test]
fn wide_multiply_constants_match_exact_oracle_at_signed_boundaries() {
    let samples = [
        i128::MIN,
        i128::MIN + 1,
        -((1i128 << 100) + 1),
        -(1i128 << 64),
        i128::from(i64::MIN),
        -2,
        -1,
        0,
        1,
        2,
        i128::from(u64::MAX),
        1i128 << 100,
        i128::MAX - 1,
        i128::MAX,
    ];
    let (min, max) = MachineIntegerType::Int128.format().bounds();
    for left in samples {
        for right in samples {
            let product = BigInt::from(left) * BigInt::from(right);
            let outcome = evaluated(c_multiply(c_int128_literal(left), c_int128_literal(right)));
            if product < min || product > max {
                assert_eq!(
                    outcome,
                    CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
                    "{left} * {right}"
                );
            } else {
                let CExpressionOutcome::Value(value) = outcome else {
                    panic!("{left} * {right}: {outcome:?}")
                };
                assert_eq!(value.c_type(), CType::Int128);
                assert_eq!(
                    MachineIntegerType::Int128
                        .constant_from_value(&value)
                        .unwrap()
                        .to_integer(),
                    product
                );
            }
        }
    }
}

#[test]
fn wide_multiply_promotes_narrow_operands_before_multiplying() {
    for (left, right, expected) in [
        (
            c_int128_literal(2),
            c_uint64_literal(u64::MAX),
            BigInt::from(u64::MAX) * 2,
        ),
        (
            c_cast(c_int64_literal(i64::MIN), CType::Int128),
            c_int32_literal(i32::MIN as u32),
            BigInt::from(i64::MIN) * BigInt::from(i32::MIN),
        ),
        (
            c_int32_literal((-1i32) as u32),
            c_int128_literal(i128::MIN + 1),
            -BigInt::from(i128::MIN + 1),
        ),
        (
            CExpression::Value(CValue::Bool(Bitvector32Term::Constant(1))),
            c_int128_literal(i128::MIN),
            BigInt::from(i128::MIN),
        ),
    ] {
        let CExpressionOutcome::Value(value) = evaluated(c_multiply(left, right)) else {
            panic!("valid wide product")
        };
        assert_eq!(
            MachineIntegerType::Int128
                .constant_from_value(&value)
                .unwrap()
                .to_integer(),
            expected
        );
    }
    // Casting the result cannot rescue overflow that occurred at the source width.
    assert_eq!(
        evaluated(c_cast(
            c_multiply(c_int64_literal(i64::MAX), c_int32_literal(2)),
            CType::Int128
        )),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow)
    );
    assert_eq!(
        evaluated(c_multiply(
            c_int128_literal(0),
            c_divide(c_int64_literal(1), c_int64_literal(0))
        )),
        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero)
    );
}

#[test]
fn wide_multiply_unknown_bounds_retain_normal_and_both_overflow_paths() {
    let (_, bounds) = product_and_bounds(MachineIntegerType::Int128, MachineIntegerType::Int128);
    for provided in 0..=2 {
        let mut assumptions = PureFactContext::new();
        for bound in &bounds[..provided] {
            assumptions = assumptions.assume_condition(bound.clone(), true);
        }
        let paths = crate::kernel::eval::apply_c_multiply(
            CValue::Int128(Bitvector32Term::Variable(Variable(150_001))),
            CValue::Int128(Bitvector32Term::Variable(Variable(150_002))),
            Vec::new(),
            Vec::new(),
            &assumptions,
        );
        assert_eq!(paths.len(), 3 - provided);
        let normals: Vec<_> = paths
            .iter()
            .filter(|path| matches!(path.outcome, CExpressionOutcome::Value(_)))
            .collect();
        assert_eq!(normals.len(), 1);
        let normal = normals[0];
        for bound in &bounds[provided..] {
            assert!(
                normal.facts.iter().any(
                    |fact| fact.proposition() == &Proposition::ConditionIs(bound.clone(), true)
                )
            );
        }
        assert!(
            paths
                .iter()
                .filter(|path| matches!(
                    path.outcome,
                    CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow)
                ))
                .count()
                == 2 - provided
        );
    }
    let expression = c_multiply(
        CExpression::Value(CValue::Int128(Bitvector32Term::Variable(Variable(150_001)))),
        CExpression::Value(CValue::Int128(Bitvector32Term::Variable(Variable(150_002)))),
    );
    assert!(prove_c_expression_evaluation(CState::new(), expression).is_none());
}

#[test]
fn wide_multiply_checked_product_bounds_certificate_discharges_native_guards() {
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };
    let x = IntegerTerm::from_machine(
        MachineIntegerType::Int64,
        Bitvector32Term::Variable(Variable(150_001)),
    )
    .unwrap();
    let y = IntegerTerm::from_machine(
        MachineIntegerType::Int32,
        Bitvector32Term::Variable(Variable(150_002)),
    )
    .unwrap();
    let le = |a, b| Proposition::ConditionIs(ConditionTerm::integer_less_equal(a, b), true);
    let premises = vec![
        le(IntegerTerm::constant(i64::MIN.into()), x.clone()),
        le(x.clone(), IntegerTerm::constant(i64::MAX.into())),
        le(IntegerTerm::constant(i32::MIN.into()), y.clone()),
        le(y.clone(), IntegerTerm::constant(i32::MAX.into())),
    ];
    let (product, _) = product_and_bounds(MachineIntegerType::Int64, MachineIntegerType::Int32);
    let (min, max) = MachineIntegerType::Int128.format().bounds();
    let goals = [
        le(IntegerTerm::constant(min), product.clone()),
        le(product.clone(), IntegerTerm::constant(max)),
    ];
    let mut assumptions = PureFactContext::new();
    for goal in goals {
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerProductBounds {
                bounds: vec![0, 1, 2, 3],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        assert_eq!(certificate.check(&goal, &premises), Ok(()));
        let Proposition::ConditionIs(condition, true) = goal else {
            unreachable!()
        };
        assumptions = assumptions.assume_condition(condition, true);
    }
    let state = CState::new()
        .with_local(
            "left",
            CValue::Int64(Bitvector32Term::Variable(Variable(150_001))),
        )
        .with_local(
            "right",
            CValue::Int32(Bitvector32Term::Variable(Variable(150_002))),
        );
    let expression = c_multiply(
        c_cast(c_variable("left"), CType::Int128),
        c_variable("right"),
    );
    let paths = evaluate_c_expression_paths(
        &state,
        &expression,
        &assumptions,
        &mut ExecutionBudget::for_c_expression(&expression),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    assert_eq!(
        paths[0].outcome,
        CExpressionOutcome::Value(CValue::Int128(Bitvector32Term::IntegerToMachine {
            value: product.into(),
            destination: MachineIntegerType::Int128
        }))
    );
}

#[test]
fn wide_multiply_unsupported_unsigned_and_noninteger_operands_stay_refused() {
    for expression in [
        c_multiply(c_int128_literal(1), c_uint128_literal(1)),
        c_multiply(c_uint128_literal(1), c_int128_literal(1)),
        c_multiply(c_uint128_literal(1), c_uint128_literal(1)),
        c_multiply(c_int128_literal(1), c_float64_literal(0)),
        c_multiply(c_int128_literal(1), c_void_value()),
    ] {
        assert_eq!(
            evaluated(expression),
            CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        );
    }
}

#[test]
fn wide_multiply_calls_keep_wide_result_and_caller_storage() {
    let function = c_function(
        CType::Int128,
        "wide_product",
        vec![
            c_parameter("left", CType::Int128),
            c_parameter("right", CType::Int128),
        ],
        c_return(c_multiply(c_variable("left"), c_variable("right"))),
    );
    let state = CState::new().with_local("caller", int32(77));
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function,
        vec![c_int64_literal(i64::MIN), c_int32_literal(i32::MIN as u32)],
        PureFactContext::new(),
    )
    .unwrap();
    let Proposition::CFunctionExecutes {
        outcome:
            CFunctionOutcome::Return {
                state: returned,
                value,
            },
        ..
    } = theorem.proposition()
    else {
        panic!("{:?}", theorem.proposition())
    };
    assert_eq!(**returned, state);
    assert_eq!(
        MachineIntegerType::Int128
            .constant_from_value(value)
            .unwrap()
            .to_integer(),
        BigInt::from(i64::MIN) * BigInt::from(i32::MIN)
    );
}

#[test]
fn wide_multiply_known_bounds_work_does_not_scan_unrelated_ambient_facts() {
    let (_, bounds) = product_and_bounds(MachineIntegerType::Int128, MachineIntegerType::Int128);
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions
                .assume_condition(ConditionTerm::Variable(Variable(151_000 + index)), true);
        }
        for bound in &bounds {
            assumptions = assumptions.assume_condition(bound.clone(), true);
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::eval::apply_c_multiply(
                CValue::Int128(Bitvector32Term::Variable(Variable(150_001))),
                CValue::Int128(Bitvector32Term::Variable(Variable(150_002))),
                Vec::new(),
                Vec::new(),
                &assumptions,
            )
        });
        assert_eq!(paths.len(), 1);
        assert!(work < 4096, "{size}: {work}");
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
        "{samples:?}"
    );
}

#[test]
fn wide_multiply_resolves_indexed_narrow_inputs_with_their_signedness() {
    for (ty, input, expected) in [
        (
            MachineIntegerType::Int64,
            Bitvector32Term::Int64Constant(i64::MIN),
            BigInt::from(i64::MIN) * 2,
        ),
        (
            MachineIntegerType::UInt64,
            Bitvector32Term::UInt64Constant(u64::MAX),
            BigInt::from(u64::MAX) * 2,
        ),
    ] {
        let variable = Bitvector32Term::Variable(Variable(153_000));
        let condition = if ty == MachineIntegerType::Int64 {
            ConditionTerm::int64_equal(variable.clone(), input)
        } else {
            ConditionTerm::uint64_equal(variable.clone(), input)
        };
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions
                    .assume_condition(ConditionTerm::Variable(Variable(154_000 + index)), true);
            }
            assumptions = assumptions.assume_condition(condition.clone(), true);
            let widened = Bitvector32Term::machine_integer_cast(
                ty,
                MachineIntegerType::Int128,
                variable.clone(),
            );
            let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::eval::apply_c_multiply(
                    CValue::Int128(widened),
                    MachineIntegerType::Int128
                        .constant_value(
                            MachineIntegerConstant::from_signed(
                                MachineIntegerType::Int128.format(),
                                2,
                            )
                            .unwrap(),
                        )
                        .unwrap(),
                    Vec::new(),
                    Vec::new(),
                    &assumptions,
                )
            });
            assert_eq!(paths.len(), 1);
            assert!(paths[0].obligations.is_empty());
            let CExpressionOutcome::Value(value) = &paths[0].outcome else {
                panic!("known bounded product")
            };
            assert_eq!(
                MachineIntegerType::Int128
                    .constant_from_value(value)
                    .unwrap()
                    .to_integer(),
                expected
            );
            assert!(work < 4096, "{size}: {work}");
            samples.push(work);
        }
        assert!(
            samples.iter().max().unwrap() - samples.iter().min().unwrap() <= 64,
            "{samples:?}"
        );
    }
}
