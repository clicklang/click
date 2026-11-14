use super::*;

fn nonnegative_i() -> SpecProposition {
    SpecProposition::Comparison {
        left: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
        operator: ComparisonOperator::LessEqual,
        right: SpecExpression::ProgramExpression(c_variable("i")),
    }
}

fn check(proposition: SpecProposition) -> LoopInvariantCheck {
    LoopInvariantCheck::new(proposition, None, None)
}

/// A loop head that cannot assume its invariants names the first declaration
/// that left it no context, by position, rather than only `false == true`.
#[test]
fn head_refusal_names_the_invariant_that_contradicts_the_ones_before_it() {
    let state = ExecutionState::new()
        .with_local("i", ProgramValue::Int32(MachineTerm::Variable(Variable(7))));
    let checks = [
        check(nonnegative_i()),
        check(SpecProposition::Not(Box::new(nonnegative_i()))),
    ];
    let (contexts, refusal) = assume_invariant_checks_explained(
        &state,
        &state,
        &checks,
        &IntegerTerm::var(Variable(9_999)),
        &PureFactContext::new(),
        &ExecutionFacts::new(),
        &[],
        &mut ExecutionBudget::default(),
    )
    .expect("lowering stays within budget");
    assert!(contexts.is_empty());
    let refusal = refusal.expect("the empty head names its cause");
    assert_eq!(refusal.declaration, 1);
    assert_eq!(
        refusal.describe(),
        "the loop head cannot assume invariant 2: assuming it contradicts the invariants \
         before it and the facts the loop keeps"
    );

    let (contexts, refusal) = assume_invariant_checks_explained(
        &state,
        &state,
        &checks[..1],
        &IntegerTerm::var(Variable(9_999)),
        &PureFactContext::new(),
        &ExecutionFacts::new(),
        &[],
        &mut ExecutionBudget::default(),
    )
    .expect("lowering stays within budget");
    assert_eq!(contexts.len(), 1);
    assert!(refusal.is_none());
}
