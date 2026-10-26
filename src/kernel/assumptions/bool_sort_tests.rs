//! The `Bool` sort's logic rules in the fact context and the e-graph
//! (`design/machine-integers.md`, Stage 5; `kernel/primitives/bool_sort.rs`):
//! L-If opened on demand, L-Eq merging two values' classes, L-Unfold's
//! defining equation, and the traversals the sort's value forms take part in.

use super::*;
use crate::kernel::VerificationSession;

pub(super) fn binder(id: u64) -> ConditionTerm {
    ConditionTerm::Variable(Variable(id))
}

pub(super) fn word(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

/// `x > 0` over the `int32` word `x`.
pub(super) fn positive(id: u64) -> ConditionTerm {
    ConditionTerm::signed_greater_than(word(id), Bitvector32Term::Constant(0))
}

/// The application `name(x)` of a `-> Bool` function to the `int32` word `x`.
pub(super) fn applied(name: &str, id: u64) -> ConditionTerm {
    ConditionTerm::bool_application(
        name,
        vec![PureFunctionArgument::Value(CValue::Int32(word(id)))],
    )
}

pub(super) fn bool_if(
    condition: ConditionTerm,
    then_condition: ConditionTerm,
    else_condition: ConditionTerm,
) -> ConditionTerm {
    ConditionTerm::BoolIf {
        condition: Box::new(condition),
        then_condition: Box::new(then_condition),
        else_condition: Box::new(else_condition),
    }
}

pub(super) fn bool_equal(left: ConditionTerm, right: ConditionTerm) -> ConditionTerm {
    ConditionTerm::BoolEqual(Box::new(left), Box::new(right))
}

#[test]
fn the_constructors_fold_only_what_their_shape_decides() {
    let _session = VerificationSession::enter();
    let (c, a, b) = (positive(1), binder(2), binder(3));
    assert_eq!(
        ConditionTerm::bool_if(ConditionTerm::Constant(true), a.clone(), b.clone()),
        a
    );
    assert_eq!(
        ConditionTerm::bool_if(ConditionTerm::Constant(false), a.clone(), b.clone()),
        b
    );
    assert_eq!(ConditionTerm::bool_if(c.clone(), a.clone(), a.clone()), a);
    assert_eq!(
        ConditionTerm::bool_if(c.clone(), a.clone(), b.clone()),
        bool_if(c, a.clone(), b.clone())
    );
    assert_eq!(
        ConditionTerm::bool_equal(a.clone(), a.clone()),
        ConditionTerm::Constant(true)
    );
    assert_eq!(
        ConditionTerm::bool_equal(a.clone(), b.clone()),
        bool_equal(a, b)
    );
}

#[test]
fn opening_a_conditional_is_its_case_split() {
    let _session = VerificationSession::enter();
    let (c, a, b) = (positive(10), binder(11), binder(12));
    let split = bool_if(c.clone(), a.clone(), b.clone()).open_bool_if(false);
    assert_eq!(
        split,
        Some(Proposition::Or(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(c.clone(), true)),
                Box::new(Proposition::ConditionIs(a.clone(), false)),
            )),
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(c, false)),
                Box::new(Proposition::ConditionIs(b, false)),
            )),
        ))
    );
    assert_eq!(binder(13).open_bool_if(true), None);
}

/// Rule L-If, decided on demand: a known condition selects its branch,
/// branches known alike decide the conditional without its condition, and
/// a conditional nothing decides stays open. Assuming a conditional files
/// it as one fact and decides nothing else.
#[test]
fn a_conditional_is_decided_by_its_condition_or_by_branches_that_agree() {
    let _session = VerificationSession::enter();
    let (c, a, b) = (positive(20), binder(21), binder(22));
    let conditional = bool_if(c.clone(), a.clone(), b.clone());
    let context = PureFactContext::new();
    assert_eq!(context.decide(&conditional), None);

    let selected = context
        .clone()
        .assume_condition(c.clone(), true)
        .assume_condition(a.clone(), true);
    assert_eq!(selected.decide(&conditional), Some(true));
    let other = context
        .clone()
        .assume_condition(c.clone(), false)
        .assume_condition(b.clone(), false);
    assert_eq!(other.decide(&conditional), Some(false));

    let agreeing = context
        .clone()
        .assume_condition(a.clone(), true)
        .assume_condition(b.clone(), true);
    assert_eq!(agreeing.decide(&conditional), Some(true));
    let disagreeing = context
        .clone()
        .assume_condition(a.clone(), true)
        .assume_condition(b.clone(), false);
    assert_eq!(disagreeing.decide(&conditional), None);

    let assumed = context.assume_condition(conditional.clone(), true);
    assert_eq!(assumed.decide(&conditional), Some(true));
    assert_eq!(assumed.decide(&c), None);
    assert_eq!(assumed.decide(&a), None);
}

/// Rule L-Eq: a true equality makes two values one class, which carries
/// either one's truth to the other, whichever was filed first.
#[test]
fn a_true_equality_carries_truth_between_its_operands_in_either_order() {
    let _session = VerificationSession::enter();
    let (application, flag) = (applied("valid", 30), binder(31));
    let equality = bool_equal(application.clone(), flag.clone());
    let fact_first = PureFactContext::new()
        .assume_condition(flag.clone(), true)
        .assume_condition(equality.clone(), true);
    assert_eq!(fact_first.decide(&application), Some(true));
    let equality_first = PureFactContext::new()
        .assume_condition(equality.clone(), true)
        .assume_condition(flag.clone(), false);
    assert_eq!(equality_first.decide(&application), Some(false));
    let from_application = PureFactContext::new()
        .assume_condition(equality, true)
        .assume_condition(application, true);
    assert_eq!(from_application.decide(&flag), Some(true));
}

/// A chain of true equalities is one class, and a false equality between
/// two of its members contradicts it.
#[test]
fn a_false_equality_contradicts_a_merge_of_its_operands() {
    let _session = VerificationSession::enter();
    let (a, b, c) = (binder(40), applied("p", 41), applied("q", 42));
    let context = PureFactContext::new()
        .assume_condition(bool_equal(a.clone(), b.clone()), true)
        .assume_condition(bool_equal(b.clone(), c.clone()), true);
    assert_eq!(
        context.decide(&bool_equal(a.clone(), c.clone())),
        Some(true)
    );
    assert!(!context.is_inconsistent());
    let contradicted = context.assume_condition(bool_equal(a, c), false);
    assert!(contradicted.is_inconsistent());
}

/// Applications of one function to equal arguments are one value.
#[test]
fn applications_to_equal_arguments_are_congruent() {
    let _session = VerificationSession::enter();
    let (left, right) = (applied("valid", 50), applied("valid", 51));
    let context = PureFactContext::new();
    assert_eq!(
        context.decide(&bool_equal(left.clone(), right.clone())),
        None
    );
    let equal_arguments = context.assume_condition(ConditionTerm::equal(word(50), word(51)), true);
    assert_eq!(
        equal_arguments.decide(&bool_equal(left.clone(), right.clone())),
        Some(true)
    );
    let known = equal_arguments.assume_condition(left, false);
    assert_eq!(known.decide(&right), Some(false));
    assert_eq!(known.decide(&applied("other", 51)), None);
}

/// Rule L-Unfold: the defining equation of `positive(x)`, whose body is
/// `x > 0`, decides the application wherever the body is decided.
#[test]
fn an_unfolded_application_has_its_body_s_truth() {
    let _session = VerificationSession::enter();
    let ConditionTerm::BoolApplication(application) = applied("positive", 60) else {
        unreachable!("an application")
    };
    let equation = ConditionTerm::bool_unfold_equation(application.clone(), positive(60));
    let context = PureFactContext::new().assume_proposition(equation);
    let applied_value = ConditionTerm::BoolApplication(application);
    assert_eq!(context.decide(&applied_value), None);
    assert_eq!(
        context
            .clone()
            .assume_condition(positive(60), true)
            .decide(&applied_value),
        Some(true)
    );
    assert_eq!(
        context
            .assume_condition(positive(60), false)
            .decide(&applied_value),
        Some(false)
    );
}

/// A read of a `bool` cell is one value per snapshot and pointer, so its
/// equality with a binder carries the binder's truth.
#[test]
fn a_bool_read_is_one_value_per_cell() {
    let _session = VerificationSession::enter();
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let read = ConditionTerm::bool_load(memory.clone(), Pointer::symbolic(Variable(70)));
    let same = ConditionTerm::bool_load(memory, Pointer::symbolic(Variable(70)));
    let context = PureFactContext::new()
        .assume_condition(bool_equal(read, binder(71)), true)
        .assume_condition(binder(71), true);
    assert_eq!(context.decide(&same), Some(true));
}

/// Substituting a word variable reaches a `Bool` value's comparisons,
/// arguments and read addresses.
#[test]
fn substitution_reaches_every_part_of_a_bool_value() {
    let _session = VerificationSession::enter();
    let value = bool_if(
        positive(80),
        applied("valid", 80),
        bool_equal(binder(81), positive(80)),
    );
    let rewritten = crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
        &value,
        Variable(80),
        &word(82),
    );
    assert_eq!(
        rewritten,
        bool_if(
            positive(82),
            applied("valid", 82),
            bool_equal(binder(81), positive(82)),
        )
    );
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::collect_condition_bitvector_variables(&rewritten, &mut variables);
    assert!(variables.contains(&Variable(82)));
    assert!(!variables.contains(&Variable(80)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/assumptions/bool_sort_tests.rs");
}
