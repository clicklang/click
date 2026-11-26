// `defined` over C fragments whose operators read an operand only under a
// guard. Contracts cannot spell these operators; they reach `defined` through
// program-side facts.
use super::*;

fn int32_value(id: u64) -> ProgramExpression {
    ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(id))))
}

fn lower(fragment: ProgramExpression) -> (Proposition, Vec<ProofObligation>) {
    let _session = crate::kernel::VerificationSession::enter();
    let (claim, _, obligations, _) =
        crate::kernel::program_lower_spec_proposition_with_checked_obligations(
            &ExecutionState::new(),
            &SpecProposition::OperationDefined(SpecExpression::ProgramExpression(fragment)),
            None,
            &PureFactContext::new(),
        )
        .unwrap();
    (claim, obligations)
}

// `x && y / x` claims nothing of its own and owes the division's domain only
// where `x` is nonzero.
#[test]
fn a_logical_and_owes_its_right_side_only_under_its_left() {
    let (x, y) = (int32_value(698_000), int32_value(698_001));
    let (claim, obligations) = lower(ProgramExpression::And(
        Box::new(x.clone()),
        Box::new(ProgramExpression::Divide(Box::new(y), Box::new(x))),
    ));
    assert!(is_true(&claim), "claim: {claim:?}");
    assert!(!obligations.is_empty());
    for obligation in &obligations {
        assert!(
            matches!(obligation.proposition(), Proposition::Implies(..)),
            "unguarded: {obligation:?}"
        );
    }
}

// `x || y / z` owes the division's domain only where `x` is zero.
#[test]
fn a_logical_or_owes_its_right_side_only_where_its_left_fails() {
    let (x, y, z) = (
        int32_value(698_010),
        int32_value(698_011),
        int32_value(698_012),
    );
    let (claim, obligations) = lower(ProgramExpression::Or(
        Box::new(x),
        Box::new(ProgramExpression::Divide(Box::new(y), Box::new(z))),
    ));
    assert!(!obligations.is_empty());
    assert!(is_true(&claim), "claim: {claim:?}");
    for obligation in &obligations {
        assert!(
            matches!(obligation.proposition(), Proposition::Implies(..)),
            "unguarded: {obligation:?}"
        );
    }
}

// `c ? y / x : 0` claims the division where `c` holds and owes nothing.
#[test]
fn a_ternary_claims_its_taken_branch_root() {
    let (c, x, y) = (
        int32_value(698_020),
        int32_value(698_021),
        int32_value(698_022),
    );
    let (claim, obligations) = lower(ProgramExpression::Ternary {
        condition: Box::new(c),
        then_branch: Box::new(ProgramExpression::Divide(Box::new(y), Box::new(x))),
        else_branch: Box::new(crate::kernel::program_expression::int32_literal(0)),
    });
    assert!(!is_true(&claim), "claim: {claim:?}");
    assert!(obligations.is_empty(), "obligations: {obligations:?}");
}

// `x != 0 and y / x > 0`: a C fragment reports its domain as a path
// condition, which the conjunction owes only where its left side holds.
#[test]
fn a_conjunction_guards_its_right_sides_path_conditions() {
    let _session = crate::kernel::VerificationSession::enter();
    let (x, y) = (int32_value(698_030), int32_value(698_031));
    let zero =
        || SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(0));
    let proposition = SpecProposition::And(
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(x.clone()),
            operator: ComparisonOperator::NotEqual,
            right: zero(),
        }),
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(ProgramExpression::Divide(
                Box::new(y),
                Box::new(x),
            )),
            operator: ComparisonOperator::GreaterThan,
            right: zero(),
        }),
    );
    let (_, facts, obligations, _) =
        crate::kernel::program_lower_spec_proposition_with_checked_obligations(
            &ExecutionState::new(),
            &proposition,
            None,
            &PureFactContext::new(),
        )
        .unwrap();
    assert!(facts.is_empty(), "unguarded path conditions: {facts:?}");
    assert!(!obligations.is_empty());
    for obligation in &obligations {
        assert!(
            matches!(obligation.proposition(), Proposition::Implies(..)),
            "unguarded: {obligation:?}"
        );
    }
}

// `x || y / x` reads `y / x` only where `x` is zero, where the division is
// undefined on every path. The refusal names the undefined behavior instead
// of only counting paths.
#[test]
fn a_right_side_undefined_wherever_it_is_read_is_refused_by_name() {
    let _session = crate::kernel::VerificationSession::enter();
    let (x, y) = (int32_value(698_040), int32_value(698_041));
    let refusal = crate::kernel::program_lower_spec_proposition_with_checked_obligations(
        &ExecutionState::new(),
        &SpecProposition::OperationDefined(SpecExpression::ProgramExpression(
            ProgramExpression::Or(
                Box::new(x.clone()),
                Box::new(ProgramExpression::Divide(Box::new(y), Box::new(x))),
            ),
        )),
        None,
        &PureFactContext::new(),
    )
    .unwrap_err();
    assert_eq!(
        refusal.message,
        "the kernel lowering produced no path: every evaluation path ended in undefined \
         behavior: division by zero"
    );
}
