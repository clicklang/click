use super::*;
#[test]
fn wide_multiply_integer_capture_requires_both_native_product_bounds() {
    let left = CValue::Int128(Bitvector32Term::Variable(Variable(150_011)));
    let right = CValue::Int128(Bitvector32Term::Variable(Variable(150_012)));
    let product = IntegerTerm::multiply(
        IntegerTerm::from_machine(
            MachineIntegerType::Int128,
            c_value_bitvector_term(&left).unwrap(),
        )
        .unwrap(),
        IntegerTerm::from_machine(
            MachineIntegerType::Int128,
            c_value_bitvector_term(&right).unwrap(),
        )
        .unwrap(),
    );
    let (min, max) = MachineIntegerType::Int128.format().bounds();
    let bounds = [
        ConditionTerm::integer_greater_equal(product.clone(), IntegerTerm::constant(min)),
        ConditionTerm::integer_less_equal(product.clone(), IntegerTerm::constant(max)),
    ];
    let native = c_multiply(CExpression::Value(left), CExpression::Value(right));
    let observation =
        SpecIntegerExpression::FromMachine(Box::new(SpecExpression::CExpression(native.clone())));
    for selected in [vec![], vec![0], vec![1], vec![0, 1]] {
        let mut assumptions = PureFactContext::new();
        for index in &selected {
            assumptions = assumptions.assume_condition(bounds[*index].clone(), true);
        }
        let capture = capture_spec_integer_value(&CState::new(), &observation, None, &assumptions);
        assert_eq!(
            capture.is_ok(),
            selected.len() == 2,
            "bounds {selected:?}: {capture:?}"
        );
        if selected.len() == 2 {
            let native_paths = evaluate_spec_expression_paths_with_loop_entry_in(
                &CState::new(),
                &SpecExpression::CExpression(native.clone()),
                None,
                &assumptions,
                &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
            )
            .unwrap();
            let specified_paths = evaluate_spec_expression_paths_with_loop_entry_in(
                &CState::new(),
                &SpecExpression::IntegerToMachine {
                    value: Box::new(SpecIntegerExpression::Term(product.clone())),
                    destination: MachineIntegerType::Int128,
                },
                None,
                &assumptions,
                &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
            )
            .unwrap();
            assert_eq!(native_paths.len(), 1);
            assert_eq!(specified_paths.len(), 1);
            assert_eq!(native_paths[0].value, specified_paths[0].value);
            assert!(native_paths[0].obligations.is_empty());
            assert!(specified_paths[0].obligations.is_empty());
        }
    }
    let overflow = SpecIntegerExpression::FromMachine(Box::new(SpecExpression::CExpression(
        c_multiply(c_int128_literal(i128::MIN), c_int128_literal(-1)),
    )));
    assert!(
        capture_spec_integer_value(&CState::new(), &overflow, None, &PureFactContext::new())
            .is_err()
    );
}
#[test]
fn wide_scalar_integer_conversion_checks_bounds_and_keeps_symbolic_obligations() {
    for destination in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let convert = |integer: IntegerTerm| {
            evaluate_spec_expression_paths_with_loop_entry_in(
                &CState::new(),
                &SpecExpression::IntegerToMachine {
                    value: Box::new(SpecIntegerExpression::Term(integer)),
                    destination,
                },
                None,
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut ExecutionBudget::default()),
            )
        };
        let (min, max) = destination.format().bounds();
        for integer in [min.clone(), max.clone()] {
            let paths = convert(IntegerTerm::constant(integer.clone())).unwrap();
            assert_eq!(paths.len(), 1);
            let value = destination.constant_from_value(&paths[0].value).unwrap();
            assert_eq!(value.to_integer(), integer);
            assert!(paths[0].obligations.is_empty());
        }
        assert!(convert(IntegerTerm::constant(min - 1)).is_err());
        assert!(convert(IntegerTerm::constant(max + 1)).is_err());
        let paths = convert(IntegerTerm::Variable(Variable(148_005))).unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value.c_type(), destination.c_type());
        assert_eq!(paths[0].obligations.len(), 2);
        assert!(paths[0].obligations.iter().any(|obligation| matches!(
            obligation.proposition(),
            Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(_, _), true)
        )));
        assert!(paths[0].obligations.iter().any(|obligation| matches!(
            obligation.proposition(),
            Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(_, _), true)
        )));
    }
}
