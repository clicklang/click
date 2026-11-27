//! The program operations on slices (`design/rust-slice-values.md`, step
//! 3a), Rust MIR's `PtrMetadata`: `s.len()` and `s.as_ptr()` read a wide
//! pointer's components in place, and `slice::from_raw_parts(p, n)` builds
//! one from a thin pointer and a count, evaluated as the spec operations of
//! 2b-iii-c-i are.
use super::*;
use crate::kernel::VerificationSession;

fn count(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn thin_of(id: u64, program_type: ProgramType) -> Pointer {
    Pointer::new(Address::symbolic(Variable(id)), program_type)
}

fn thin(id: u64) -> Pointer {
    thin_of(id, ProgramType::UInt8Pointer)
}

fn named_slice(id: u64) -> ProgramValue {
    crate::kernel::symbolic_call_result(
        ProgramType::SlicePointer(SliceElement::UInt8),
        Variable(id),
    )
}

fn value(value: ProgramValue) -> Box<ProgramExpression> {
    Box::new(ProgramExpression::Value(value))
}

fn pointer(pointer: &Pointer) -> Box<ProgramExpression> {
    value(ProgramValue::Pointer(pointer.clone()))
}

fn from_raw_parts(
    data: Box<ProgramExpression>,
    count: Box<ProgramExpression>,
) -> ProgramExpression {
    ProgramExpression::SliceFromRawParts { data, count }
}

/// The one outcome `expression` evaluates to at an empty state, with no fact
/// added and nothing owed.
fn evaluated(expression: &ProgramExpression) -> ExpressionOutcome {
    let mut paths = evaluate_program_expression_paths(
        &ExecutionState::new(),
        expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::for_program_expression(expression),
    )
    .unwrap();
    assert_eq!(paths.len(), 1, "{paths:?}");
    let path = paths.remove(0);
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    assert!(path.facts.is_empty(), "{:?}", path.facts);
    path.outcome
}

fn evaluated_value(expression: &ProgramExpression) -> ProgramValue {
    match evaluated(expression) {
        ExpressionOutcome::Value(value) => value,
        other => panic!("expected a value, got {other:?}"),
    }
}

/// `slice::from_raw_parts(p, n)` is the wide pointer with thin part `p` and
/// count `n`, and its components are `p` and `n` themselves, with no unfold.
#[test]
fn a_constructed_slice_has_its_parts_as_components() {
    let _session = VerificationSession::enter();
    let built = from_raw_parts(
        pointer(&thin(975_000)),
        value(ProgramValue::UInt64(count(975_001))),
    );
    let ProgramValue::Pointer(slice) = evaluated_value(&built) else {
        panic!("a construction is a pointer value");
    };
    assert_eq!(slice, thin(975_000).with_element_count(count(975_001)));
    assert_eq!(
        evaluated_value(&ProgramExpression::SliceLength(Box::new(built.clone()))),
        ProgramValue::UInt64(count(975_001))
    );
    assert_eq!(
        evaluated_value(&ProgramExpression::SliceData(Box::new(built))),
        ProgramValue::Pointer(thin(975_000))
    );
}

/// Every slice equals `from_raw_parts(s.as_ptr(), s.len())` by construction
/// (requirement 7's eta), here for a slice a call returned, named by its
/// counted variable.
#[test]
fn a_named_slice_rebuilds_from_its_components() {
    let _session = VerificationSession::enter();
    let named = named_slice(975_010);
    let rebuilt = from_raw_parts(
        Box::new(ProgramExpression::SliceData(value(named.clone()))),
        Box::new(ProgramExpression::SliceLength(value(named.clone()))),
    );
    assert_eq!(evaluated_value(&rebuilt), named);
    let ProgramValue::UInt64(OldMachineTerm::Variable(length)) =
        evaluated_value(&ProgramExpression::SliceLength(value(named)))
    else {
        panic!("a named slice's count is its counted variable");
    };
    assert_eq!(length.counted_slice(), Some(Variable(975_010)));
}

/// A component read of a thin pointer or a scalar is a type mismatch that
/// names the operation; a construction from a wide pointer is refused,
/// naming `.as_ptr()`; one from a pointer no slice has, or with a count that
/// is not a `u64`, is a type mismatch, as the spec operations refuse them.
#[test]
fn slice_operations_refuse_operands_of_the_wrong_kind() {
    let _session = VerificationSession::enter();
    assert_eq!(
        evaluated(&ProgramExpression::SliceLength(pointer(&thin(975_020)))),
        ExpressionOutcome::RuntimeError(RuntimeError::SliceTypeMismatch {
            operation: "`.len()`"
        })
    );
    assert_eq!(
        evaluated(&ProgramExpression::SliceData(value(ProgramValue::UInt64(
            count(975_021)
        )))),
        ExpressionOutcome::RuntimeError(RuntimeError::SliceTypeMismatch {
            operation: "`.as_ptr()`"
        })
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            value(named_slice(975_022)),
            value(ProgramValue::UInt64(count(975_023)))
        )),
        ExpressionOutcome::RuntimeError(RuntimeError::ThinPointerRequired {
            operation: "`slice::from_raw_parts`",
        })
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            pointer(&thin_of(975_024, ProgramType::VoidPointer)),
            value(ProgramValue::UInt64(count(975_025)))
        )),
        ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            pointer(&thin(975_026)),
            value(ProgramValue::Int32(count(975_027)))
        )),
        ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch)
    );
    assert!(
        RuntimeError::slice_type_mismatch_message("`.len()`").contains("`.len()` takes a slice")
    );
}

/// A slice's data pointer steps by an element: `s.as_ptr() + 1` of a `[u32]`
/// is the thin pointer one `u32` on, as for the thin pointer itself.
#[test]
fn a_slice_data_pointer_steps_by_its_element() {
    let _session = VerificationSession::enter();
    let data = thin_of(975_030, ProgramType::UInt32Pointer);
    let slice = data.clone().with_element_count(count(975_031));
    let one = value(ProgramValue::Int32(OldMachineTerm::constant(1)));
    let through_slice = ProgramExpression::Add(
        Box::new(ProgramExpression::SliceData(pointer(&slice))),
        one.clone(),
    );
    let through_construction = ProgramExpression::Add(
        Box::new(ProgramExpression::SliceData(Box::new(from_raw_parts(
            pointer(&data),
            value(ProgramValue::UInt64(count(975_031))),
        )))),
        one.clone(),
    );
    let direct = ProgramExpression::Add(pointer(&data), one);
    let state = ExecutionState::new();
    for expression in [&through_slice, &through_construction] {
        assert_eq!(
            crate::kernel::eval::program_expression_pointee_type(&state, expression),
            Some(ProgramType::UInt32)
        );
    }
    let direct = evaluated(&direct);
    assert_eq!(evaluated(&through_slice), direct);
    assert_eq!(evaluated(&through_construction), direct);
}

/// The program-expression walks see through the operations to their
/// operands: a binding mention and a variable substitution.
#[test]
fn program_expression_walks_reach_slice_operands() {
    let _session = VerificationSession::enter();
    let s = BindingName::from("s");
    let t = BindingName::from("t");
    let expression = from_raw_parts(
        Box::new(ProgramExpression::SliceData(Box::new(
            ProgramExpression::Variable(s.clone()),
        ))),
        Box::new(ProgramExpression::SliceLength(Box::new(
            ProgramExpression::Variable(t.clone()),
        ))),
    );
    let mut names = std::collections::BTreeSet::new();
    crate::kernel::termination::collect_program_expression_variables(&expression, &mut names);
    assert!(names.contains(&s) && names.contains(&t), "{names:?}");

    let substituted = |expression: ProgramExpression| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_program_expression(
            &ProgramExpression::SliceLength(Box::new(expression)),
            Variable(975_041),
            &OldMachineTerm::uint64_constant(5),
        )
    };
    assert_eq!(
        substituted(from_raw_parts(
            pointer(&thin(975_040)),
            value(ProgramValue::UInt64(count(975_041)))
        )),
        ProgramExpression::SliceLength(Box::new(from_raw_parts(
            pointer(&thin(975_040)),
            value(ProgramValue::UInt64(OldMachineTerm::uint64_constant(5)))
        )))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/program_slice_operation_tests.rs");
}
