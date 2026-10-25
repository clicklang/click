//! The Integer conditional, `IntegerTerm::If`, mirrors the machine
//! `Bitvector32Term::If`: built without a decided condition or equal arms,
//! and reduced to one arm by a rewrite that decides its condition.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn integer(id: u64) -> IntegerTerm {
    IntegerTerm::var(Variable(id))
}

fn is_zero(id: u64) -> ConditionTerm {
    ConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: CompareRelation::Equal,
        left: Box::new(Bitvector32Term::Variable(Variable(id))),
        right: Box::new(Bitvector32Term::Constant(0)),
    }
}

fn successor(id: u64) -> IntegerTerm {
    IntegerTerm::add(integer(id), IntegerTerm::constant_i64(1))
}

#[test]
fn integer_conditional_is_built_only_when_undecided_with_distinct_arms() {
    assert_eq!(
        IntegerTerm::if_then_else(ConditionTerm::Constant(true), integer(1), integer(2)),
        integer(1)
    );
    assert_eq!(
        IntegerTerm::if_then_else(ConditionTerm::Constant(false), integer(1), integer(2)),
        integer(2)
    );
    assert_eq!(
        IntegerTerm::if_then_else(is_zero(7), successor(1), successor(1)),
        successor(1)
    );
    let conditional = IntegerTerm::if_then_else(is_zero(7), successor(1), integer(2));
    let IntegerTerm::If {
        then_term,
        else_term,
        ..
    } = &conditional
    else {
        panic!("an undecided conditional stands: {conditional}");
    };
    // The arms are shared nodes, so rebuilding the conditional reuses them.
    assert_eq!(*then_term, SharedIntegerTerm::from(successor(1)));
    assert_eq!(*else_term, SharedIntegerTerm::from(integer(2)));
    assert_eq!(
        SharedIntegerTerm::from(conditional.clone()),
        SharedIntegerTerm::from(IntegerTerm::if_then_else(
            is_zero(7),
            successor(1),
            integer(2)
        ))
    );
    // Its condition is part of its identity.
    assert_ne!(
        conditional,
        IntegerTerm::if_then_else(is_zero(8), successor(1), integer(2))
    );
}

#[test]
fn integer_conditional_is_one_arm_once_a_rewrite_decides_its_condition() {
    let conditional = IntegerTerm::if_then_else(is_zero(7), successor(1), integer(2));
    let variable = Bitvector32Term::Variable(Variable(7));
    let (zero, one) = (Bitvector32Term::Constant(0), Bitvector32Term::Constant(1));
    assert_eq!(
        TermRewrite::for_bits(&variable, &zero).integer(&conditional),
        successor(1)
    );
    assert_eq!(
        TermRewrite::for_bits(&variable, &one).integer(&conditional),
        integer(2)
    );
    // A known condition decides it, as it decides a machine conditional.
    let known = HashMap::from([(is_zero(7), false)]);
    assert_eq!(
        TermRewrite::for_conditions(&known).integer(&conditional),
        integer(2)
    );
    let unrelated = HashMap::from([(is_zero(8), true)]);
    assert_eq!(
        TermRewrite::for_conditions(&unrelated).integer(&conditional),
        conditional
    );
}

#[test]
fn an_exact_integer_rewrite_that_makes_the_arms_equal_leaves_one_arm() {
    // `rewrite(x == y)` on `if c { x } else { y }` leaves `y`, as the
    // machine rewrite does, so `normalize` sees `y == y`.
    let conditional = IntegerTerm::if_then_else(is_zero(7), integer(1), integer(2));
    let (from, to) = (
        SharedIntegerTerm::from(integer(1)),
        SharedIntegerTerm::from(integer(2)),
    );
    assert_eq!(
        TermRewrite::for_integer_exact(&from, &to).integer(&conditional),
        integer(2)
    );
    // Arms it leaves distinct keep the conditional's shape.
    let other = SharedIntegerTerm::from(integer(3));
    let IntegerTerm::If { else_term, .. } =
        TermRewrite::for_integer_exact(&from, &other).integer(&conditional)
    else {
        panic!("distinct arms keep the conditional");
    };
    assert_eq!(else_term, SharedIntegerTerm::from(integer(2)));
}

#[test]
fn integer_conditionals_are_alpha_equivalent_exactly_when_their_parts_are() {
    let left = SharedIntegerTerm::from(IntegerTerm::if_then_else(
        is_zero(7),
        successor(1),
        integer(2),
    ));
    let same = SharedIntegerTerm::from(IntegerTerm::if_then_else(
        is_zero(7),
        successor(1),
        integer(2),
    ));
    let swapped = SharedIntegerTerm::from(IntegerTerm::if_then_else(
        is_zero(7),
        integer(2),
        successor(1),
    ));
    assert_eq!(
        crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(&left, &same),
        Some(true)
    );
    assert_eq!(
        crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(&left, &swapped),
        Some(false)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/integer_conditional_tests.rs");
}
