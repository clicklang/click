use super::*;

/// A bound occurrence of the binder with this variable. The Surface
/// resolves every bound occurrence to the binder's variable; the kernel
/// never binds a quantifier by its source spelling.
fn bound(variable: Variable) -> SpecExpression {
    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)))
}

fn positive(expression: SpecExpression) -> SpecProposition {
    SpecProposition::Comparison {
        left: expression,
        operator: CComparisonOperator::GreaterThan,
        right: SpecExpression::Value(int32(0)),
    }
}

fn universal(body: SpecProposition) -> SpecProposition {
    SpecProposition::ForAllInt32 {
        name: "k".to_string(),
        variable: Variable(41),
        body: Box::new(body),
    }
}

fn introductions(proposition: &SpecProposition) -> LoweringIntroductions {
    let (_, _, _, introductions) =
        crate::kernel::c_lower_spec_proposition_at_state_with_provenance(
            &CState::new(),
            proposition,
            None,
            &PureFactContext::new(),
        )
        .expect("the test proposition lowers on one path");
    introductions
}

#[test]
fn inequality_lowering_records_its_negation() {
    let algebraic = |index| SpecAlgebraicExpression {
        algebraic_type: AlgebraicType::parameter("T".into()),
        node: SpecAlgebraicExpressionNode::Variable(Variable(index)),
    };
    let sequence =
        |value| SpecSequenceExpression::Literal(vec![SpecExpression::Value(int32(value))]);
    for equal in [false, true] {
        for source in [
            SpecProposition::AlgebraicComparison {
                left: algebraic(1),
                equal,
                right: algebraic(2),
            },
            SpecProposition::SequenceComparison {
                left: sequence(1),
                equal,
                right: sequence(2),
            },
        ] {
            let (goal, _, _, recorded) =
                crate::kernel::c_lower_spec_proposition_at_state_with_provenance(
                    &CState::new(),
                    &source,
                    None,
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(matches!(goal, Proposition::Not(_)), !equal);
            assert_eq!(
                recorded,
                if equal {
                    vec![]
                } else {
                    vec![LoweringIntroduction::ComparisonNegation]
                },
                "{source:?}"
            );
        }
    }
}

#[test]
fn a_written_universal_over_a_written_implication_records_both() {
    let recorded = introductions(&universal(SpecProposition::Implies(
        Box::new(positive(bound(Variable(41)))),
        Box::new(positive(bound(Variable(41)))),
    )));

    assert_eq!(
        recorded,
        vec![
            LoweringIntroduction::WrittenUniversal {
                name: "k".to_string(),
                variable: Variable(41),
                pointer: false,
                integer: false,
            },
            LoweringIntroduction::WrittenImplication,
        ]
    );
}

#[test]
fn a_definedness_guard_is_recorded_before_the_written_implication() {
    // `k + 1` may overflow for an unconstrained `k`, so lowering keeps
    // the defined path and folds its no-overflow fact into an implication
    // that no spec, and therefore no Surface, connective wrote.
    let incremented = || {
        SpecExpression::Add(
            Box::new(bound(Variable(41))),
            Box::new(SpecExpression::Value(int32(1))),
        )
    };
    let recorded = introductions(&universal(SpecProposition::Implies(
        Box::new(positive(incremented())),
        Box::new(positive(incremented())),
    )));

    assert_eq!(
        recorded,
        vec![
            LoweringIntroduction::WrittenUniversal {
                name: "k".to_string(),
                variable: Variable(41),
                pointer: false,
                integer: false,
            },
            LoweringIntroduction::PathFactGuard,
            LoweringIntroduction::WrittenImplication,
        ]
    );
}

fn existential(body: SpecProposition) -> SpecProposition {
    SpecProposition::ExistsInt32 {
        name: "len".to_string(),
        variable: Variable(41),
        body: Box::new(body),
    }
}

/// A definedness guard for an expression over an existentially bound
/// name belongs under the binder that binds it. Hoisting it leaves the
/// bound variable free in the guard and bound in the body, which is a
/// proposition no Surface proof can state or introduce.
#[test]
fn a_definedness_guard_under_an_existential_stays_under_its_binder() {
    let incremented = SpecExpression::Add(
        Box::new(bound(Variable(41))),
        Box::new(SpecExpression::Value(int32(1))),
    );
    let (goal, facts, obligations, recorded) =
        crate::kernel::c_lower_spec_proposition_at_state_with_provenance(
            &CState::new(),
            &existential(positive(incremented)),
            None,
            &PureFactContext::new(),
        )
        .expect("the existential lowers on one path");

    let overflows = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(
            Bitvector32Term::Variable(Variable(41)),
            Bitvector32Term::Constant(1),
        ),
        false,
    );
    let Proposition::Exists { var, body, .. } = &goal else {
        panic!("the lowered goal is an existential, got {goal:?}");
    };
    assert_eq!(*var, Variable(41));
    // A guard restricts an existential's witness, so it is a conjunct of
    // the quantified body, not an antecedent: an implication would make
    // the claim vacuously true of every witness the guard excludes.
    let Proposition::And(guard, _) = body.as_ref() else {
        panic!("the guard is the head conjunct of the quantified body, got {body:?}");
    };
    assert_eq!(guard.as_ref(), &overflows);

    // Nothing the lowering published beside the goal may mention the
    // bound variable, and every obligation must rebind it itself.
    assert!(
        facts.is_empty(),
        "the binder's path facts escaped: {facts:?}"
    );
    for obligation in &obligations {
        let Proposition::Exists { var, .. } = obligation else {
            panic!("an obligation escaped its binder: {obligation:?}");
        };
        assert_eq!(*var, Variable(41));
    }

    // The head chain describes what an introduction reaches first. The
    // guard is not there, so the chain must not claim it is.
    assert_eq!(recorded, Vec::new());
}

#[test]
fn an_integer_existential_does_not_expose_nested_introductions_at_its_head() {
    let body = SpecProposition::ForAllInt32 {
        name: "k".to_string(),
        variable: Variable(42),
        body: Box::new(positive(bound(Variable(42)))),
    };
    let proposition = SpecProposition::ExistsInteger {
        name: "z".to_string(),
        variable: Variable(43),
        body: Box::new(body),
    };

    let (_, _, _, recorded) = crate::kernel::c_lower_spec_proposition_at_state_with_provenance(
        &CState::new(),
        &proposition,
        None,
        &PureFactContext::new(),
    )
    .expect("the nested quantified proposition lowers on one path");

    // The `witness`/`choose` step must consume the existential before any
    // introduction below its body becomes reachable.
    assert!(
        recorded.is_empty(),
        "unexpected existential head chain: {recorded:?}"
    );
}
