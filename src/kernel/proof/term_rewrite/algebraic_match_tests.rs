use super::*;

fn tree_type() -> AlgebraicType {
    let key = AlgebraicValueType::Algebraic {
        name: "Tree".into(),
        arguments: vec![],
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Empty".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Pair".into(),
            fields: vec![key.clone(), key.clone()],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: "Tree".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
    }
}
fn value(node: AlgebraicTermNode) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: tree_type(),
        node,
    }
}
fn var(id: u64) -> AlgebraicTerm {
    value(AlgebraicTermNode::Variable(Variable(id)))
}
fn empty() -> AlgebraicTerm {
    value(AlgebraicTermNode::Constructor {
        variant: "Empty".into(),
        fields: vec![],
    })
}
fn pair(a: AlgebraicTerm, b: AlgebraicTerm) -> AlgebraicTerm {
    value(AlgebraicTermNode::Constructor {
        variant: "Pair".into(),
        fields: vec![AlgebraicValue::Algebraic(a), AlgebraicValue::Algebraic(b)],
    })
}
fn select(scrutinee: AlgebraicTerm, a: u64, b: u64, body: AlgebraicTerm) -> AlgebraicTerm {
    value(AlgebraicTermNode::Match {
        scrutinee: Box::new(scrutinee),
        arms: vec![
            AlgebraicResultMatchArm {
                variant: "Empty".into(),
                bindings: vec![],
                body: empty(),
            },
            AlgebraicResultMatchArm {
                variant: "Pair".into(),
                bindings: vec![
                    AlgebraicValue::Algebraic(var(a)),
                    AlgebraicValue::Algebraic(var(b)),
                ],
                body,
            },
        ],
    })
}
fn normalizes(a: AlgebraicTerm, b: AlgebraicTerm) -> bool {
    crate::kernel::proof::fact_reasoning::normalizes_context_free(&Proposition::Equal(
        Term::Algebraic(a),
        Term::Algebraic(b),
    ))
}

#[test]
fn algebraic_match_normalization_substitutes_simultaneously_and_reduces_nested_matches() {
    let input = select(pair(var(2), empty()), 1, 2, pair(var(1), var(2)));
    assert!(normalizes(input.clone(), pair(var(2), empty())));
    assert!(!normalizes(input, pair(empty(), empty())));
    let inner = select(var(1), 3, 4, var(3));
    let nested = select(pair(pair(var(9), empty()), empty()), 1, 2, inner);
    assert!(normalizes(nested, var(9)));
    assert!(!normalizes(select(var(9), 1, 2, var(1)), empty()));
}

#[test]
fn algebraic_match_normalization_avoids_capturing_a_field_under_a_nested_binder() {
    let inner = select(var(8), 3, 4, pair(var(1), var(3)));
    let input = select(pair(var(3), empty()), 1, 2, inner);
    let reduced = TermRewrite::normalize_algebraic(&input).unwrap();
    let AlgebraicTermNode::Match { arms, .. } = reduced.node else {
        panic!("symbolic match must remain")
    };
    let arm = &arms[1];
    assert_ne!(arm.bindings[0], AlgebraicValue::Algebraic(var(3)));
    let AlgebraicTermNode::Constructor { fields, .. } = &arm.body.node else {
        panic!("expected pair")
    };
    assert_eq!(fields[0], AlgebraicValue::Algebraic(var(3)));
    assert_eq!(fields[1], arm.bindings[0]);
}

#[test]
fn algebraic_match_normalization_refuses_malformed_matches() {
    let valid = select(pair(empty(), empty()), 1, 2, var(1));
    for mutation in 0..6 {
        let mut malformed = valid.clone();
        let AlgebraicTermNode::Match { scrutinee, arms } = &mut malformed.node else {
            unreachable!()
        };
        match mutation {
            0 => {
                arms.pop();
            }
            1 => {
                arms[0].variant = "Pair".into();
            }
            2 => {
                arms[1].bindings.pop();
            }
            3 => {
                arms[1].bindings[1] = arms[1].bindings[0].clone();
            }
            4 => {
                arms[1].bindings[0] = AlgebraicValue::Algebraic(empty());
            }
            5 => {
                let AlgebraicTermNode::Constructor { fields, .. } = &mut scrutinee.node else {
                    unreachable!()
                };
                fields.pop();
            }
            _ => unreachable!(),
        }
        assert!(
            TermRewrite::normalize_algebraic(&malformed).is_none(),
            "mutation {mutation}"
        );
        assert!(!normalizes(malformed, empty()), "mutation {mutation}");
    }
}

#[test]
fn algebraic_match_normalization_work_scales_with_the_selected_expression() {
    let matched = select(pair(empty(), empty()), 1, 2, var(1));
    let mut one = TermRewrite::empty();
    assert_eq!(one.algebraic(&matched), empty());
    assert!(one.refusal().is_none());
    for size in [16, 64, 256, 1024] {
        let input = value(AlgebraicTermNode::PureFunctionApplication {
            name: "opaque".into(),
            arguments: vec![PureFunctionArgument::Algebraic(matched.clone()); size],
        });
        let mut rewrite = TermRewrite::empty();
        let reduced = rewrite.algebraic(&input);
        assert!(rewrite.refusal().is_none());
        assert_eq!(rewrite.visits, 1 + size * one.visits);
        let AlgebraicTermNode::PureFunctionApplication { arguments, .. } = reduced.node else {
            panic!("function must stay opaque")
        };
        assert!(
            arguments
                .iter()
                .all(|arg| arg == &PureFunctionArgument::Algebraic(empty()))
        );
    }
}

#[test]
fn algebraic_match_normalization_substitutes_integer_fields() {
    let key = AlgebraicValueType::Algebraic {
        name: "Box".into(),
        arguments: vec![],
    };
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
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
    };
    let boxed = |field| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Box".into(),
            fields: vec![AlgebraicValue::Integer(field)],
        },
    };
    let expected = boxed(IntegerTerm::Variable(Variable(7)));
    let input = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Match {
            scrutinee: Box::new(expected.clone()),
            arms: vec![AlgebraicResultMatchArm {
                variant: "Box".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(1)))],
                body: boxed(IntegerTerm::Variable(Variable(1))),
            }],
        },
    };
    assert!(normalizes(input.clone(), expected));
    assert!(!normalizes(
        input,
        boxed(IntegerTerm::Variable(Variable(8)))
    ));
}
