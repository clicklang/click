//! Slice-valued pure applications (`design/rust-slice-values.md`, step
//! 2b-iii-b-ii): `f(x)` of slice type is the wide pointer whose thin part is
//! based on the application and whose count is the application's count, and
//! a pass that rewrites the application's arguments rewrites the count's.
use super::*;
use crate::kernel::VerificationSession;

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

fn int32(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn application(id: u64) -> SharedPureApplication {
    SharedPureApplication::intern(
        "bytes_of".into(),
        vec![PureFunctionArgument::Value(ProgramValue::Int32(int32(id)))],
    )
}

fn call(result_type: ProgramType, id: u64) -> SpecExpression {
    SpecExpression::PureFunctionApplication {
        name: "bytes_of".into(),
        arguments: vec![SpecPureFunctionArgument::Value(SpecExpression::Value(
            ProgramValue::Int32(int32(id)),
        ))],
        result_type,
        pointer_result: None,
        result_object_class: None,
    }
}

fn evaluated(expression: &SpecExpression, legacy: bool) -> (SpecValue, Pointer) {
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    budget.machine_preparation_disabled = legacy;
    budget.machine_result_production_disabled = legacy;
    let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&ExecutionState::new(), None),
        expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    let value = paths.remove(0).value;
    let ProgramValue::Pointer(pointer) = value.clone().into_native() else {
        panic!("a slice application is a pointer value");
    };
    (value, pointer)
}

/// The application's value is a wide pointer: its thin part is based on the
/// application at the element's pointer type, and its count is the
/// application's count, never an integer application of `bytes_of`. The
/// shared and native producers agree, and a `str` keeps its type.
#[test]
fn a_slice_application_names_both_components() {
    let _session = VerificationSession::enter();
    let (shared, slice) = evaluated(&call(bytes(), 967_000), false);
    assert!(matches!(
        shared.shared().map(KernelTerm::node),
        Some(KernelTermNode::PointerCall { .. })
    ));
    assert!(slice.is_wide());
    assert_eq!(slice.program_type(), bytes());
    let thin = slice.as_ptr();
    assert_eq!(thin.program_type(), ProgramType::UInt8Pointer);
    assert_eq!(
        thin.address().base,
        AddressBase::PureFunctionApplication(application(967_000))
    );
    assert_eq!(
        slice.len(),
        Some(&OldMachineTerm::pure_application_count(application(
            967_000
        )))
    );
    assert_eq!(evaluated(&call(bytes(), 967_000), true).1, slice);
    assert_ne!(
        evaluated(&call(bytes(), 967_001), false).1.len(),
        slice.len()
    );

    let text = ProgramType::SlicePointer(SliceElement::Str);
    let (_, string) = evaluated(&call(text, 967_000), false);
    assert_eq!(string.program_type(), text);
    assert_eq!(string.len(), slice.len());
}

/// Substituting `y` for `x` in `bytes_of(x).len()`, or closing over and
/// renaming `x` in `bytes_of(x).len() == 7`, rewrites the count's application
/// as it rewrites the thin part's.
#[test]
fn rewriting_a_count_rewrites_its_application() {
    let _session = VerificationSession::enter();
    let (x, y) = (Variable(967_010), Variable(967_011));
    let count = |id| OldMachineTerm::pure_application_count(application(id));
    assert_eq!(
        crate::kernel::reasoning::substitute_bitvector_variable(
            &count(967_010),
            x,
            &int32(967_011)
        ),
        count(967_011)
    );
    let fact = |id| {
        Proposition::condition_is(
            OldConditionTerm::uint64_equal(count(id), OldMachineTerm::uint64_constant(7)),
            true,
        )
    };

    let closed = crate::kernel::quantifiers::close_forall(
        BinderName::default(),
        x,
        Sort::ProgramInt32,
        &fact(967_010),
    )
    .expect("an int32 quantifier closes");
    let Proposition::ForAll { var, body, .. } = &closed else {
        panic!("a universal: {closed:?}");
    };
    assert_ne!(
        **body,
        fact(967_010),
        "closing rewrites the count's argument"
    );
    let renamed =
        crate::kernel::quantifiers::rename_quantified_variable(body, **var, y, &Sort::ProgramInt32)
            .expect("renames");
    assert_eq!(renamed, fact(967_011));
}
