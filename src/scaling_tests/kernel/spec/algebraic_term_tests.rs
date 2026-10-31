// Scaling tests of `src/kernel/spec.rs` (module `algebraic_term_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn algebraic_integer_match_scales_with_nested_depth() {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Box".into(),
        fields: vec![AlgebraicValueType::Integer],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "Box".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "Box".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let mut previous = None;
    for depth in [8, 16, 32, 64] {
        let mut expression = SpecAlgebraicExpression {
            algebraic_type: ty.clone(),
            node: SpecAlgebraicExpressionNode::Constructor {
                variant: "Box".into(),
                fields: vec![SpecAlgebraicValue::Integer(SpecIntegerExpression::Term(
                    IntegerTerm::var(Variable(100_000 + depth as u64 - 1)),
                ))],
            },
        };
        for level in (0..depth).rev() {
            expression = SpecAlgebraicExpression {
                algebraic_type: ty.clone(),
                node: SpecAlgebraicExpressionNode::Match {
                    scrutinee: Box::new(SpecAlgebraicExpression {
                        algebraic_type: ty.clone(),
                        node: SpecAlgebraicExpressionNode::Variable(Variable(
                            200_000 + level as u64,
                        )),
                    }),
                    arms: vec![SpecAlgebraicResultMatchArm {
                        variant: "Box".into(),
                        bindings: vec![format!("n{level}")],
                        binding_types: vec![AlgebraicValueType::Integer],
                        binding_variables: vec![Some(Variable(100_000 + level as u64))],
                        body: Box::new(expression),
                    }],
                },
            };
        }
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_algebraic_at_state_in(
                &CState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap()
        });
        assert!(
            budget.integer_bindings.is_empty(),
            "arm scopes must be restored"
        );
        assert_eq!(paths.len(), 1);
        let mut value = &paths[0].value;
        let mut last_binding = None;
        for _ in 0..depth {
            let AlgebraicTermNode::Match { arms, .. } = &value.node else {
                panic!("expected nested match");
            };
            last_binding = Some(arms[0].bindings[0].clone());
            value = &arms[0].body;
        }
        let AlgebraicTermNode::Constructor { fields, .. } = &value.node else {
            panic!("expected payload constructor");
        };
        assert_eq!(fields, &vec![last_binding.unwrap()]);
        assert!(work <= 256 * depth + 128, "depth {depth}: {work}");
        if let Some(previous) = previous {
            assert!(
                work <= previous * 5 / 2 + 64,
                "nested match work must remain linear: {previous} -> {work}"
            );
        }
        previous = Some(work);
    }
}

#[test]
fn signed_match_definedness_does_not_scan_constructor_facts() {
    for related in [false, true] {
        let mut work = Vec::new();
        for size in [8u64, 16, 32, 64] {
            let mut context = PureFactContext::new();
            let constructor = maybe_constructor(Some(int32(7)));
            for index in 0..size {
                let right = if related && index > 0 {
                    maybe_variable(Variable(1_000 + index - 1))
                } else {
                    constructor.clone()
                };
                context = context.assume_proposition(Proposition::Equal(
                    Term::Algebraic(maybe_variable(Variable(1_000 + index))),
                    Term::Algebraic(right),
                ));
            }
            let expression = signed_value_or_match(Variable(1_000 + size - 1));
            let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
                evaluate_spec_expression_paths_with_loop_entry_in(
                    &CState::new(),
                    &expression,
                    None,
                    &context,
                    &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
                )
                .unwrap()
            });
            assert_eq!(paths.len(), 1);
            assert!(!paths[0].obligations.is_empty());
            work.push(measured);
        }
        assert!(
            work.windows(2)
                .all(|pair| pair[1] <= pair[0] + pair[0] / 4 + 16),
            "related={related}, work={work:?}"
        );
    }
}
