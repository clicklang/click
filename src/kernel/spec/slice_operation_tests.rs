//! The spec operations on slices (`design/rust-slice-values.md`, step
//! 2b-iii-c-i): `s.len()` and `s.as_ptr()` read a wide pointer's components
//! in place, and `slice::from_raw_parts(p, n)` builds one from a thin pointer
//! and a count, owing nothing.
use super::*;
use crate::kernel::VerificationSession;

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

fn value(value: ProgramValue) -> Box<SpecExpression> {
    Box::new(SpecExpression::Value(value))
}

fn thin(id: u64) -> ProgramValue {
    crate::kernel::symbolic_call_result(ProgramType::UInt8Pointer, Variable(id))
}

fn count(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn named_slice(id: u64) -> ProgramValue {
    crate::kernel::symbolic_call_result(bytes(), Variable(id))
}

fn from_raw_parts(data: ProgramValue, count: ProgramValue) -> SpecExpression {
    SpecExpression::SliceFromRawParts {
        data: value(data),
        count: value(count),
    }
}

/// The one value `expression` evaluates to, with the shared producers on,
/// or the runtime error its evaluation dropped.
fn evaluated(expression: &SpecExpression) -> Result<ProgramValue, RuntimeError> {
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&ExecutionState::new(), None),
        expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap();
    if paths.is_empty() {
        return Err(budget
            .dropped_runtime_error
            .clone()
            .expect("an evaluation with no value drops its error"));
    }
    assert_eq!(paths.len(), 1);
    let path = paths.remove(0);
    assert!(path.obligations.is_empty(), "{:?}", path.obligations);
    Ok(path.value.into_native())
}

/// `slice::from_raw_parts(p, n)` is the wide pointer with thin part `p` and
/// count `n`, and its components are `p` and `n` themselves, with no unfold.
#[test]
fn a_constructed_slice_has_its_parts_as_components() {
    let _session = VerificationSession::enter();
    let built = from_raw_parts(thin(968_000), ProgramValue::UInt64(count(968_001)));
    let Ok(ProgramValue::Pointer(slice)) = evaluated(&built) else {
        panic!("a construction is a pointer value");
    };
    assert!(slice.is_wide());
    assert_eq!(slice.program_type(), bytes());
    assert_eq!(slice.len(), Some(&count(968_001)));
    assert_eq!(ProgramValue::Pointer(slice.as_ptr()), thin(968_000));

    assert_eq!(
        evaluated(&SpecExpression::SliceLength(Box::new(built.clone()))),
        Ok(ProgramValue::UInt64(count(968_001)))
    );
    assert_eq!(
        evaluated(&SpecExpression::SliceData(Box::new(built))),
        Ok(thin(968_000))
    );
}

/// The components of a named slice are its named thin part and the count
/// its name gives (2b-iii-a); rebuilding the slice from them gives the same
/// value, so every slice equals `from_raw_parts(s.as_ptr(), s.len())`.
#[test]
fn a_named_slice_rebuilds_from_its_components() {
    let _session = VerificationSession::enter();
    let named = named_slice(968_010);
    let ProgramValue::Pointer(slice) = &named else {
        panic!("a slice is a pointer value");
    };
    let length = evaluated(&SpecExpression::SliceLength(value(named.clone()))).unwrap();
    assert_eq!(
        length,
        ProgramValue::UInt64(slice.len().expect("a wide pointer").clone())
    );
    let ProgramValue::UInt64(OldMachineTerm::Variable(variable)) = &length else {
        panic!("a named slice's count is a variable: {length:?}");
    };
    assert_eq!(variable.counted_slice(), Some(Variable(968_010)));
    let data = evaluated(&SpecExpression::SliceData(value(named.clone()))).unwrap();
    assert_eq!(
        evaluated(&SpecExpression::SliceFromRawParts {
            data: value(data),
            count: value(length),
        }),
        Ok(named)
    );
}

/// A component of a thin pointer, a construction from a wide pointer, from a
/// pointer no slice has, or with a count that is not a `u64` is refused.
#[test]
fn slice_operations_refuse_operands_of_the_wrong_kind() {
    let _session = VerificationSession::enter();
    assert_eq!(
        evaluated(&SpecExpression::SliceLength(value(thin(968_020)))),
        Err(RuntimeError::TypeMismatch)
    );
    assert_eq!(
        evaluated(&SpecExpression::SliceData(value(ProgramValue::UInt64(
            count(968_021)
        )))),
        Err(RuntimeError::TypeMismatch)
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            named_slice(968_022),
            ProgramValue::UInt64(count(968_023))
        )),
        Err(RuntimeError::ThinPointerRequired {
            operation: "`slice::from_raw_parts`",
        })
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            crate::kernel::symbolic_call_result(ProgramType::VoidPointer, Variable(968_024)),
            ProgramValue::UInt64(count(968_025))
        )),
        Err(RuntimeError::TypeMismatch)
    );
    assert_eq!(
        evaluated(&from_raw_parts(
            thin(968_026),
            ProgramValue::Int32(count(968_027))
        )),
        Err(RuntimeError::TypeMismatch)
    );
}

/// A slice application's components are its thin part and its count, the
/// application's own (2b-iii-b-ii), read from the value with no unfold.
#[test]
fn a_slice_application_has_its_components() {
    let _session = VerificationSession::enter();
    let call = SpecExpression::PureFunctionApplication {
        name: "bytes_of".into(),
        arguments: vec![SpecPureFunctionArgument::Value(SpecExpression::Value(
            ProgramValue::Int32(count(968_030)),
        ))],
        result_type: bytes(),
        pointer_result: None,
        result_object_class: None,
    };
    let application = SharedPureApplication::intern(
        "bytes_of".into(),
        vec![PureFunctionArgument::Value(ProgramValue::Int32(count(
            968_030,
        )))],
    );
    assert_eq!(
        evaluated(&SpecExpression::SliceLength(Box::new(call.clone()))),
        Ok(ProgramValue::UInt64(
            OldMachineTerm::pure_application_count(application.clone())
        ))
    );
    let Ok(ProgramValue::Pointer(data)) = evaluated(&SpecExpression::SliceData(Box::new(call)))
    else {
        panic!("a slice's data is a pointer value");
    };
    assert!(!data.is_wide());
    assert_eq!(data.program_type(), ProgramType::UInt8Pointer);
    assert_eq!(
        data.address().base,
        AddressBase::PureFunctionApplication(application)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/slice_operation_tests.rs");
}
