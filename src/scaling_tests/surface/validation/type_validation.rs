// Scaling tests of src/surface/validation/type_validation.rs.
use super::*;

#[test]
fn typed_lambda_validation_scales_with_body_and_ignores_unrelated_bindings() {
    let mut baseline = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let mut variables = BTreeMap::new();
            let mut integers = BTreeSet::new();
            for index in 0..unrelated {
                variables.insert(format!("unused{index}"), InterfaceType::Int32);
                integers.insert(format!("unused_integer{index}"));
            }
            let mut level = (0..size)
                .map(|index| {
                    let name = format!("capture{index}");
                    integers.insert(name.clone());
                    ContractExpression::Binding(name)
                })
                .collect::<Vec<_>>();
            while level.len() > 1 {
                level = level
                    .chunks_exact(2)
                    .map(|pair| {
                        ContractExpression::Add(
                            Box::new(pair[0].clone()),
                            Box::new(pair[1].clone()),
                        )
                    })
                    .collect();
            }
            let expression = ContractExpression::Lambda {
                parameters: vec![("x".into(), ClickType::Integer)],
                result: ClickType::Integer,
                body: Box::new(level.pop().unwrap()),
            };
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                infer_scoped_spec_value_type(
                    &expression,
                    &variables,
                    &integers,
                    &BTreeMap::new(),
                    "lambda scaling",
                    false,
                )
            });
            assert!(matches!(result.unwrap(), SpecValueType::Function(_)));
            assert!(work > 0);
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "lambda body work must remain near-linear: {costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "lambda typing must not scan unrelated bindings"
            );
        }
    }
}

#[test]
fn lambda_fold_typing_scales_with_captures_and_ignores_unrelated_bindings() {
    let mut baseline = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let mut variables = BTreeMap::new();
            let mut integers = BTreeSet::new();
            for index in 0..unrelated {
                variables.insert(format!("unused{index}"), InterfaceType::Int32);
                integers.insert(format!("unused_integer{index}"));
            }
            let mut level = (0..size)
                .map(|index| {
                    let name = format!("capture{index}");
                    integers.insert(name.clone());
                    ContractExpression::Binding(name)
                })
                .collect::<Vec<_>>();
            while level.len() > 1 {
                level = level
                    .chunks_exact(2)
                    .map(|pair| {
                        ContractExpression::Add(
                            Box::new(pair[0].clone()),
                            Box::new(pair[1].clone()),
                        )
                    })
                    .collect();
            }
            let step = ContractExpression::Lambda {
                parameters: vec![
                    ("acc".into(), ClickType::Integer),
                    ("k".into(), ClickType::Program(InterfaceType::Int32)),
                ],
                result: ClickType::Integer,
                body: Box::new(ContractExpression::Add(
                    Box::new(ContractExpression::Binding("acc".into())),
                    Box::new(level.pop().unwrap()),
                )),
            };
            let literal = |value| {
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(MachineTerm::uint32_constant(value)),
                ))
            };
            let expression = lambdas::range_fold(
                literal(0),
                literal(3),
                ContractExpression::IntegerLiteral("0".into()),
                step,
            );
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                infer_scoped_spec_value_type(
                    &expression,
                    &variables,
                    &integers,
                    &BTreeMap::new(),
                    "fold scaling",
                    true,
                )
            });
            assert_eq!(result.unwrap(), SpecValueType::Integer);
            assert!(work > 0);
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "fold step work must remain near-linear: {costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "fold typing must not scan unrelated bindings"
            );
        }
    }
}

#[test]
fn proposition_lambda_and_range_validation_ignore_unrelated_scopes() {
    let mut baseline = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let mut variables = BTreeMap::new();
            let mut integers = BTreeSet::new();
            for index in 0..unrelated {
                variables.insert(format!("unused{index}"), InterfaceType::Int32);
                integers.insert(format!("unused_integer{index}"));
            }
            let mut level = (0..size)
                .map(|index| {
                    let name = format!("capture{index}");
                    integers.insert(name.clone());
                    ClickProposition::Comparison {
                        left: ContractExpression::Binding(name.clone()),
                        operator: ComparisonOperator::Equal,
                        right: ContractExpression::Binding(name),
                    }
                })
                .collect::<Vec<_>>();
            while level.len() > 1 {
                level = level
                    .chunks_exact(2)
                    .map(|pair| {
                        ClickProposition::And(Box::new(pair[0].clone()), Box::new(pair[1].clone()))
                    })
                    .collect();
            }
            let predicate = ContractExpression::Lambda {
                parameters: vec![("x".into(), ClickType::Program(InterfaceType::Int32))],
                result: ClickType::Proposition,
                body: Box::new(ContractExpression::Proposition(Box::new(
                    level.pop().unwrap(),
                ))),
            };
            let literal = |value| {
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(MachineTerm::uint32_constant(value)),
                ))
            };
            let all = lambdas::range_proposition(literal(0), literal(3), predicate, true);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_theorem_proposition_expression_types(
                    &all,
                    &variables,
                    &integers,
                    &BTreeMap::new(),
                    "proposition scaling",
                )
            });
            result.unwrap();
            assert!(work > 0);
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "proposition work must remain near-linear: {costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "proposition validation must not scan unrelated scopes"
            );
        }
    }
}

#[test]
fn memory_lambda_validation_scales_with_reads_and_ignores_unrelated_bindings() {
    let template = parser::parse("theorem test() { ensures true; }").unwrap();
    let mut baseline = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let mut costs = Vec::new();
        for size in [8, 16, 32, 64] {
            let mut variables = BTreeMap::new();
            let mut integers = BTreeSet::new();
            for index in 0..unrelated {
                variables.insert(format!("unused{index}"), InterfaceType::Int32);
                integers.insert(format!("unused_integer{index}"));
            }
            let mut level = (0..size)
                .map(|index| {
                    let name = format!("capture{index}");
                    variables.insert(name.clone(), InterfaceType::Int32Pointer);
                    ContractExpression::Index(
                        Box::new(ContractExpression::Binding(name)),
                        Box::new(ContractExpression::Binding("x".into())),
                    )
                })
                .collect::<Vec<_>>();
            while level.len() > 1 {
                level = level
                    .chunks_exact(2)
                    .map(|pair| {
                        ContractExpression::Add(
                            Box::new(pair[0].clone()),
                            Box::new(pair[1].clone()),
                        )
                    })
                    .collect();
            }
            let expression = ContractExpression::Lambda {
                parameters: vec![("x".into(), ClickType::Program(InterfaceType::Int32))],
                result: ClickType::Program(InterfaceType::Int32),
                body: Box::new(level.pop().unwrap()),
            };
            let mut clause = template.theorem_definitions()[0].ensures()[0].clone();
            clause.proof_bindings = vec![("unused".into(), None, expression.clone())];
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let result = infer_scoped_spec_value_type(
                    &expression,
                    &variables,
                    &integers,
                    &BTreeMap::new(),
                    "lambda scaling",
                    false,
                )?;
                validate_declaration_lambda_bindings(
                    &[clause],
                    &variables,
                    &integers,
                    &BTreeMap::new(),
                    "declaration scaling",
                )?;
                Ok::<_, ClickError>(result)
            });
            assert!(matches!(result.unwrap(), SpecValueType::Function(_)));
            assert!(work > 0);
            costs.push(work);
        }
        for pair in costs.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0],
                "lambda body work must remain near-linear: {costs:?}"
            );
        }
        if unrelated == 0 {
            baseline = costs;
        } else {
            assert_eq!(
                costs, baseline,
                "lambda typing must not scan unrelated bindings"
            );
        }
    }
}
