use super::*;

fn schema(fields: Vec<AlgebraicValueType>) -> AlgebraicVariantType {
    AlgebraicVariantType {
        name: "Case".into(),
        fields,
    }
}

fn arm(
    binding_types: Vec<AlgebraicValueType>,
    binding_variables: Vec<Option<Variable>>,
) -> SpecIntegerMatchArm {
    SpecIntegerMatchArm {
        variant: "Case".into(),
        bindings: (0..binding_types.len())
            .map(|index| format!("binding{index}"))
            .collect(),
        binding_types,
        binding_variables,
        body: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
    }
}

#[test]
fn integer_match_metadata_rejects_missing_integer_identity() {
    let integer = AlgebraicValueType::Integer;
    assert!(!spec_integer_match_arm_is_well_formed(
        &schema(vec![integer.clone()]),
        &arm(vec![integer], vec![None]),
    ));
}

#[test]
fn integer_match_metadata_rejects_c_identity_and_schema_mismatch() {
    let integer = AlgebraicValueType::Integer;
    let c = AlgebraicValueType::C(CType::Int32);
    assert!(!spec_integer_match_arm_is_well_formed(
        &schema(vec![c.clone()]),
        &arm(vec![c.clone()], vec![Some(Variable(1))]),
    ));
    assert!(!spec_integer_match_arm_is_well_formed(
        &schema(vec![integer.clone()]),
        &arm(vec![c], vec![None]),
    ));
}

#[test]
fn integer_match_metadata_rejects_duplicate_integer_identities() {
    let integer = AlgebraicValueType::Integer;
    assert!(!spec_integer_match_arm_is_well_formed(
        &schema(vec![integer.clone(), integer.clone()]),
        &arm(
            vec![integer.clone(), integer],
            vec![Some(Variable(7)), Some(Variable(7))],
        ),
    ));
}

/// The arm body reaches the binder-elimination rewrite without the match
/// that bound it, so a free variable sharing the binder's identity is
/// indistinguishable from the binder itself. The rewrite therefore
/// substitutes only identities from the reserved match-binder range,
/// which nothing free can carry.
#[test]
fn binder_elimination_refuses_an_execution_identity_as_a_binder() {
    let havocked = Variable(ExecutionBudget::KERNEL_VARIABLE_BASE);
    assert_eq!(
        rewrite_integer_match_typed_fields(
            IntegerTerm::var(havocked),
            &[AlgebraicValue::Integer(IntegerTerm::var(havocked))],
            &[AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
        ),
        None,
        "a loop-havocked local's identity is not a binder, and rewriting \
             the body under it would capture the local"
    );
}

/// A genuine binder is eliminated, and a free identity beside it in the
/// same body is left exactly as it was.
#[test]
fn binder_elimination_leaves_a_free_identity_alone() {
    let binder = Variable(ExecutionBudget::MATCH_BINDER_VARIABLE_BASE);
    let havocked = Variable(ExecutionBudget::KERNEL_VARIABLE_BASE);
    let field = IntegerTerm::constant_i64(7);
    assert_eq!(
        rewrite_integer_match_typed_fields(
            IntegerTerm::add(IntegerTerm::var(binder), IntegerTerm::var(havocked)),
            &[AlgebraicValue::Integer(IntegerTerm::var(binder))],
            &[AlgebraicValue::Integer(field.clone())],
        ),
        Some(IntegerTerm::add(field, IntegerTerm::var(havocked))),
    );
}
