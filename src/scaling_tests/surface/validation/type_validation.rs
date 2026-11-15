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
