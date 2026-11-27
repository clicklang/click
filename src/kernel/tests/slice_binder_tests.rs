//! Slice binders (`design/rust-slice-values.md`, step 2b-iii-b-i): a binder of
//! slice sort is one variable `v` naming the wide pointer with thin part
//! `Address::symbolic(v)` and count `v.element_count()`, and closing, opening,
//! renaming and substituting it carry `v` and its count together.
use super::*;
use crate::kernel::VerificationSession;
use crate::kernel::quantifiers::{close_forall, open_quantifier, rename_quantified_variable};

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

fn slice_sort() -> Sort {
    Sort::ProgramPointer(bytes())
}

/// The slice the variable `v` names.
fn named(variable: Variable) -> Pointer {
    let Some(ProgramValue::Pointer(pointer)) = slice_sort().symbolic_pointer_value(variable) else {
        panic!("a slice sort names a slice value");
    };
    pointer
}

fn count_of(variable: Variable) -> OldMachineTerm {
    OldMachineTerm::Variable(variable.element_count())
}

/// `s.len() == 7 && s == t`: one fact about the binder's count alone and one
/// about the whole slice, beside the free slice `t`.
fn body_over(slice: &Pointer, other: Variable) -> Proposition {
    Proposition::And(
        Box::new(Proposition::condition_is(
            OldConditionTerm::uint64_equal(
                slice.len().expect("a slice has a count").clone(),
                OldMachineTerm::uint64_constant(7),
            ),
            true,
        )),
        Box::new(Proposition::condition_is(
            OldConditionTerm::pointer_equal(slice.clone(), named(other)),
            true,
        )),
    )
}

fn forall_over(binder: Variable, other: Variable) -> Proposition {
    close_forall(
        BinderName::default(),
        binder,
        slice_sort(),
        &body_over(&named(binder), other),
    )
    .expect("a slice quantifier closes")
}

fn quantifier_parts(proposition: &Proposition) -> (QuantifierBinder, &Proposition) {
    let Proposition::ForAll { var, body, .. } = proposition else {
        panic!("a universal: {proposition:?}");
    };
    (*var, body)
}

/// Closing over a slice binder takes its count with it: the body mentions the
/// bound variable's count and neither the free slice nor its count. Opening
/// gives back the body over the witness, count included.
#[test]
fn closing_and_opening_a_slice_binder_carry_its_count() {
    let _session = VerificationSession::enter();
    let (binder, other) = (Variable(966_000), Variable(966_001));
    let closed = forall_over(binder, other);
    let (var, body) = quantifier_parts(&closed);
    let variables = proposition_variables(body);
    assert!(!variables.contains(&binder), "{variables:?}");
    assert!(
        !variables.contains(&binder.element_count()),
        "the free slice's count stays free after closing: {variables:?}"
    );
    assert!(variables.contains(&var.element_count()), "{variables:?}");
    assert!(variables.contains(&other.element_count()), "{variables:?}");

    let (witness, opened) = open_quantifier(var, &slice_sort(), body).expect("opens");
    assert_eq!(opened, body_over(&named(witness), other));
}

/// A rename of a slice binder renames its count; a rename at a thin pointer
/// sort leaves a count alone, as before.
#[test]
fn renaming_a_slice_binder_renames_its_count() {
    let _session = VerificationSession::enter();
    let (from, to, other) = (Variable(966_010), Variable(966_011), Variable(966_012));
    let body = body_over(&named(from), other);
    let renamed = rename_quantified_variable(&body, from, to, &slice_sort()).expect("renames");
    assert_eq!(renamed, body_over(&named(to), other));

    let thin = Sort::ProgramPointer(ProgramType::UInt8Pointer);
    let count_only = Proposition::condition_is(
        OldConditionTerm::uint64_equal(count_of(from), OldMachineTerm::uint64_constant(7)),
        true,
    );
    assert_eq!(
        rename_quantified_variable(&count_only, from, to, &thin).expect("renames"),
        count_only,
        "a thin pointer binder names no count"
    );
}

/// Instantiating a slice quantifier with a slice value replaces the binder's
/// count by the value's count, so `s.len() == 7` becomes `n == 7`.
#[test]
fn instantiating_a_slice_binder_takes_the_value_count() {
    let _session = VerificationSession::enter();
    let (binder, other) = (Variable(966_020), Variable(966_021));
    let closed = forall_over(binder, other);
    let (var, body) = quantifier_parts(&closed);
    let value = Pointer::new(
        Address::symbolic(Variable(966_022)),
        ProgramType::UInt8Pointer,
    )
    .with_element_count(OldMachineTerm::Variable(Variable(966_023)));
    let instantiated =
        crate::kernel::substitute_pointer_value_in_proposition(body, *var, &value).unwrap();
    assert_eq!(instantiated, body_over(&value, other));
    let variables = proposition_variables(&instantiated);
    assert!(!variables.contains(&var.element_count()), "{variables:?}");
}

/// A `match` arm's slice payload is replaced, count and all, by the field it
/// binds: the typed rewrite a `match` reduction runs maps the binder's count
/// to the field's.
#[test]
fn a_slice_payload_replacement_takes_the_field_count() {
    let _session = VerificationSession::enter();
    let (binder, other) = (Variable(966_030), Variable(966_031));
    let body = body_over(&named(binder), other);
    let field = named(Variable(966_032));
    let program = std::collections::BTreeMap::from([(
        binder,
        crate::kernel::proof::term_rewrite::TypedProgramValueReplacement::Pointer(field.clone()),
    )]);
    let (integer, algebraic) = (Default::default(), Default::default());
    let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::for_typed_variables(
        &program, &integer, &algebraic,
    );
    let replaced = rewrite.substitute_proposition(&body);
    assert!(rewrite.refusal().is_none());
    assert_eq!(replaced, body_over(&field, other));
}

/// Aligning a quantified body with a target binder refuses a target whose
/// count is already free in the body: the target's count would be captured.
/// Alpha-equivalence of two slice quantifiers compares their counts too.
#[test]
fn aligning_slice_binders_respects_their_counts() {
    let _session = VerificationSession::enter();
    let (binder, other, target) = (Variable(966_040), Variable(966_041), Variable(966_042));
    let body = Proposition::And(
        Box::new(body_over(&named(binder), other)),
        Box::new(Proposition::condition_is(
            OldConditionTerm::uint64_equal(count_of(target), OldMachineTerm::uint64_constant(3)),
            true,
        )),
    );
    assert_eq!(
        crate::kernel::api::contract_certification::substitute_quantified_body_capture_free(
            &body,
            binder,
            target,
            &slice_sort(),
        ),
        None
    );
    let fresh = Variable(966_043);
    assert_eq!(
        crate::kernel::api::contract_certification::substitute_quantified_body_capture_free(
            &body_over(&named(binder), other),
            binder,
            fresh,
            &slice_sort(),
        ),
        Some(body_over(&named(fresh), other))
    );

    let left = body_over(&named(binder), other);
    let right = body_over(&named(target), other);
    assert!(
        crate::kernel::api::contract_certification::propositions_alpha_equivalent_under_binders(
            &slice_sort(),
            binder,
            &left,
            target,
            &right,
        )
    );
    // `s.len() == 7` and `t.len() == 7` under two binders that differ in
    // which count the first conjunct names are not alpha-equivalent.
    let mismatched = Proposition::And(
        Box::new(Proposition::condition_is(
            OldConditionTerm::uint64_equal(count_of(other), OldMachineTerm::uint64_constant(7)),
            true,
        )),
        Box::new(Proposition::condition_is(
            OldConditionTerm::pointer_equal(named(target), named(other)),
            true,
        )),
    );
    assert!(
        !crate::kernel::api::contract_certification::propositions_alpha_equivalent_under_binders(
            &slice_sort(),
            binder,
            &left,
            target,
            &mismatched,
        )
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/slice_binder_tests.rs");
}
