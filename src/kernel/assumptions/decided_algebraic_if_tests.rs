//! An equality between an algebraic `if` and a constructor decides the
//! condition when one branch applies a different constructor.

use super::*;

pub(super) fn option_type() -> AlgebraicType {
    let key = AlgebraicValueType::Algebraic {
        name: "Option".into(),
        arguments: vec![],
    };
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "None".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Some".into(),
            fields: vec![AlgebraicValueType::C(CType::UInt32)],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: "Option".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
    }
}
fn term(node: AlgebraicTermNode) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: option_type(),
        node,
    }
}
fn none() -> AlgebraicTerm {
    term(AlgebraicTermNode::Constructor {
        variant: "None".into(),
        fields: vec![],
    })
}
pub(super) fn some(variable: u64) -> AlgebraicTerm {
    term(AlgebraicTermNode::Constructor {
        variant: "Some".into(),
        fields: vec![AlgebraicValue::C(CValue::UInt32(
            Bitvector32Term::Variable(Variable(variable)),
        ))],
    })
}
pub(super) fn tag(variable: u64) -> ConditionTerm {
    ConditionTerm::Bitvector32Equal(
        Box::new(Bitvector32Term::Variable(Variable(variable))),
        Box::new(Bitvector32Term::Constant(0)),
    )
}
/// `if tag == 0 { None } else { Some(payload) }`, a Rust option's view.
pub(super) fn view(tag_variable: u64, payload: u64) -> AlgebraicTerm {
    term(AlgebraicTermNode::If {
        condition: Box::new(tag(tag_variable)),
        then_term: Box::new(none()),
        else_term: Box::new(some(payload)),
    })
}
pub(super) fn equal(left: AlgebraicTerm, right: AlgebraicTerm) -> Proposition {
    Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))
}
fn values_equal(left: u64, right: u64) -> ConditionTerm {
    ConditionTerm::Bitvector32Equal(
        Box::new(Bitvector32Term::Variable(Variable(left))),
        Box::new(Bitvector32Term::Variable(Variable(right))),
    )
}

#[test]
fn an_if_equal_to_the_other_branchs_constructor_decides_its_condition() {
    let context = PureFactContext::new().assume_proposition(equal(view(1, 2), some(3)));
    assert_eq!(context.decide(&tag(1)), Some(false));
    assert_eq!(context.decide(&values_equal(2, 3)), Some(true));
    let mirrored = PureFactContext::new().assume_proposition(equal(none(), view(1, 2)));
    assert_eq!(mirrored.decide(&tag(1)), Some(true));
}

#[test]
fn an_if_whose_branches_share_the_constructor_decides_nothing() {
    let both = term(AlgebraicTermNode::If {
        condition: Box::new(tag(1)),
        then_term: Box::new(some(4)),
        else_term: Box::new(some(2)),
    });
    let context = PureFactContext::new().assume_proposition(equal(both, some(3)));
    assert_eq!(context.decide(&tag(1)), None);
}

#[test]
fn a_later_fact_reads_a_decided_conditional_at_its_branch() {
    let context = PureFactContext::new()
        .assume_proposition(equal(view(1, 2), some(3)))
        .assume_proposition(equal(
            term(AlgebraicTermNode::Variable(Variable(5))),
            view(1, 2),
        ));
    assert!(context.pure_facts().contains(&equal(
        term(AlgebraicTermNode::Variable(Variable(5))),
        some(2)
    )));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/decided_algebraic_if_tests.rs");
}
