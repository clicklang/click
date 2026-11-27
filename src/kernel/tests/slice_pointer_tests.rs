//! Slice pointer types (`design/rust-slice-values.md`, step 2b-i): a wide
//! pointer's type is `ProgramType::SlicePointer`, every value of it carries
//! its element count, and no thin-pointer operation reads one.
use super::*;
use crate::kernel::VerificationSession;

fn count(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn thin(id: u64) -> Pointer {
    Pointer::new(Address::symbolic(Variable(id)), ProgramType::UInt8Pointer)
}

fn wide(pointer: u64, length: u64) -> Pointer {
    thin(pointer).with_element_count(count(length))
}

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

fn paths(expression: &ProgramExpression) -> Vec<ExpressionPath> {
    evaluate_program_expression_paths(
        &ExecutionState::new(),
        expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::for_program_expression(expression),
    )
    .unwrap()
}

fn value(pointer: &Pointer) -> Box<ProgramExpression> {
    Box::new(ProgramExpression::Value(ProgramValue::Pointer(
        pointer.clone(),
    )))
}

fn refused(paths: &[ExpressionPath]) -> Vec<&'static str> {
    paths
        .iter()
        .map(|path| match &path.outcome {
            ExpressionOutcome::RuntimeError(RuntimeError::ThinPointerRequired { operation }) => {
                *operation
            }
            other => panic!("expected a thin-pointer refusal, got {other:?}"),
        })
        .collect()
}

#[test]
fn a_wide_pointer_has_its_slice_pointer_type() {
    let _session = VerificationSession::enter();
    let s = wide(960_001, 960_002);
    assert_eq!(s.program_type(), bytes());
    assert_eq!(s.as_ptr().program_type(), ProgramType::UInt8Pointer);
    assert_eq!(s.as_ptr(), thin(960_001));
    assert_eq!(bytes().byte_width(), 16);
    assert_eq!(bytes().abi_alignment(), 8);
    assert_eq!(ProgramValue::Pointer(s.clone()).byte_width(), 16);
    assert_eq!(ProgramValue::Pointer(s.as_ptr()).byte_width(), 8);
    // No pointee type: arithmetic, ordering and dereference read the thin
    // part, never the slice.
    assert_eq!(bytes().pointee_type(), None);
    assert!(!bytes().is_pointer() && bytes().is_slice_pointer());
    assert!(bytes().accepts(&ProgramValue::Pointer(s.clone())));
    assert!(!bytes().accepts(&ProgramValue::Pointer(s.as_ptr())));
    assert!(!ProgramType::UInt8Pointer.accepts(&ProgramValue::Pointer(s.clone())));
    assert!(!ProgramType::VoidPointer.accepts(&ProgramValue::Pointer(s.clone())));
    // A generic `[T]` and `str`.
    let parameter = TypeParameterName::intern("T");
    let generic = Pointer::new(
        Address::symbolic(Variable(960_003)),
        ProgramType::ParameterPointer(parameter),
    )
    .with_element_count(count(960_004));
    assert_eq!(
        generic.program_type(),
        ProgramType::SlicePointer(SliceElement::Parameter(parameter))
    );
    assert_eq!(
        generic.as_ptr().program_type(),
        ProgramType::ParameterPointer(parameter)
    );
    let text = s
        .clone()
        .with_type(ProgramType::SlicePointer(SliceElement::Str));
    assert_eq!(text.len(), s.len());
    assert_eq!(text, s, "a retyping keeps the value");
    assert_eq!(text.as_ptr().program_type(), ProgramType::UInt8Pointer);
    assert_eq!(SliceElement::UInt8.slice_type_spelling(), "Slice<uint8>");
    assert_eq!(SliceElement::Str.slice_type_spelling(), "Str");
    // The kernel handle keeps the same invariant.
    let handle = thin(960_001).shared().with_element_count(
        crate::kernel::KernelTerm::retained_machine_operand(
            MachineIntegerType::UInt64,
            crate::kernel::MachineOperandView::Old(&count(960_002)),
        ),
    );
    assert_eq!(handle.export().unwrap(), s);
    assert_eq!(handle.export().unwrap().program_type(), bytes());
    assert_eq!(
        handle.as_ptr().export().unwrap().program_type(),
        ProgramType::UInt8Pointer
    );
}

#[test]
#[should_panic(expected = "would add or remove a slice's element count")]
fn retyping_never_widens_a_thin_pointer() {
    let _ = thin(960_010).with_type(bytes());
}

#[test]
#[should_panic(expected = "would add or remove a slice's element count")]
fn retyping_never_drops_a_count() {
    let _ = wide(960_011, 960_012).with_type(ProgramType::UInt8Pointer);
}

#[test]
#[should_panic(expected = "a slice pointer is built with its element count")]
fn a_slice_pointer_is_never_built_thin() {
    let _ = Pointer::new(Address::symbolic(Variable(960_013)), bytes());
}

#[test]
#[should_panic(expected = "is no slice's thin part")]
fn only_an_element_pointer_widens() {
    let _ = Pointer::new(
        Address::symbolic(Variable(960_014)),
        ProgramType::VoidPointer,
    )
    .with_element_count(count(960_015));
}

/// A cast between slice pointer types keeps the count, as Rust's `as`
/// between `*const [T]` and `*const [U]` does; every other cast that
/// would add or drop a count is refused.
#[test]
fn casts_keep_a_count_or_refuse() {
    let _session = VerificationSession::enter();
    let s = wide(960_020, 960_021);
    let cast = |value: ProgramValue, target| {
        crate::kernel::eval::cast_program_value_to_type(
            value,
            target,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
    };
    let retyped = cast(
        ProgramValue::Pointer(s.clone()),
        ProgramType::SlicePointer(SliceElement::Str),
    );
    let Ok(ProgramValue::Pointer(retyped)) = retyped else {
        panic!("{retyped:?}")
    };
    assert_eq!(retyped.len(), s.len());
    assert_eq!(
        retyped.program_type(),
        ProgramType::SlicePointer(SliceElement::Str)
    );
    for (value, target, operation) in [
        (
            ProgramValue::Pointer(s.clone()),
            ProgramType::UInt64,
            "a cast of a slice",
        ),
        (
            ProgramValue::Pointer(s.clone()),
            ProgramType::UInt8Pointer,
            "a cast of a slice",
        ),
        (
            ProgramValue::Pointer(s.as_ptr()),
            bytes(),
            "a cast to a slice pointer type",
        ),
        (
            ProgramValue::UInt64(count(960_022)),
            bytes(),
            "a cast to a slice pointer type",
        ),
    ] {
        assert_eq!(
            cast(value, target),
            Err(RuntimeError::ThinPointerRequired { operation })
        );
    }
}

/// Arithmetic, ordering, comparison, bitwise operations, dereference and
/// truth tests read a thin pointer. Given a slice each names itself and
/// refuses, rather than reading the slice's address and dropping its
/// count.
#[test]
fn thin_pointer_operations_refuse_a_slice() {
    let _session = VerificationSession::enter();
    let s = wide(960_030, 960_031);
    let p = s.as_ptr();
    let one = Box::new(ProgramExpression::Value(ProgramValue::Int64(
        OldMachineTerm::int64_constant(1),
    )));
    for (expression, operation) in [
        (
            ProgramExpression::Add(value(&s), one.clone()),
            "pointer arithmetic",
        ),
        (
            ProgramExpression::Add(one.clone(), value(&s)),
            "pointer arithmetic",
        ),
        (
            ProgramExpression::Subtract(value(&s), one.clone()),
            "pointer arithmetic",
        ),
        (
            ProgramExpression::Subtract(value(&s), value(&p)),
            "pointer arithmetic",
        ),
        (
            ProgramExpression::LessThan(value(&s), value(&s)),
            "an ordered pointer comparison",
        ),
        (
            ProgramExpression::Equal(value(&s), value(&s)),
            "a pointer comparison",
        ),
        (
            ProgramExpression::NotEqual(value(&p), value(&s)),
            "a pointer comparison",
        ),
        (
            ProgramExpression::BitwiseAnd(value(&s), one.clone()),
            "a bitwise operation",
        ),
        (
            ProgramExpression::PointerOffsetBytes {
                pointer: value(&s),
                bytes: crate::kernel::LayoutOffset::Bytes(8),
            },
            "a member offset",
        ),
        (
            ProgramExpression::Subobject {
                pointer: value(&s),
                width: 1,
            },
            "a member selection",
        ),
        (
            crate::kernel::program_expression::typed_load(*value(&s), ProgramType::UInt8),
            "a dereference",
        ),
        (ProgramExpression::Not(value(&s)), "a truth test"),
    ] {
        let paths = paths(&expression);
        assert!(!paths.is_empty(), "{expression:?}");
        assert!(
            refused(&paths).iter().all(|refused| *refused == operation),
            "{expression:?}: {:?}",
            refused(&paths)
        );
    }
    // The thin part is an ordinary pointer.
    let paths = paths(&ProgramExpression::Equal(value(&p), value(&p)));
    assert!(
        paths
            .iter()
            .all(|path| matches!(path.outcome, ExpressionOutcome::Value(_))),
        "{paths:?}"
    );
}

/// Two pointer values match in everything but their address only when
/// their metadata is known equal: the same count term, or counts the facts
/// make one `UInt64` class. So proving their addresses equal proves the
/// slices equal, and a slice never matches its thin part.
#[test]
fn a_slice_matches_only_a_slice_of_a_known_equal_count() {
    let _session = VerificationSession::enter();
    let (n, m) = (960_041, 960_042);
    let (s, t) = (wide(960_040, n), wide(960_040, m));
    let empty = PureFactContext::new();
    assert!(empty.pointer_provenance_match(&s, &s.clone()));
    assert!(!empty.pointer_provenance_match(&s, &t));
    assert!(!empty.pointer_provenance_match(&s, &s.as_ptr()));
    assert!(empty.pointer_provenance_match(&s.as_ptr(), &t.as_ptr()));
    let equal_counts = empty
        .clone()
        .assume_condition(OldConditionTerm::uint64_equal(count(n), count(m)), true);
    assert!(equal_counts.pointer_provenance_match(&s, &t));
    assert!(!equal_counts.pointer_provenance_match(&s, &t.as_ptr()));
    let equality = OldConditionTerm::PointerEqual(Box::new(s.clone()), Box::new(t.clone()));
    assert_eq!(empty.decide(&equality), None);
    assert_eq!(equal_counts.decide(&equality), Some(true));
    // Equal addresses in one provenance leave a slice equality open until
    // the counts are equal too.
    let u = thin(960_043).with_element_count(count(n));
    let v = thin(960_043)
        .with_address(Address::symbolic(Variable(960_044)))
        .with_element_count(count(m));
    let addresses = empty.clone().assume_condition(
        OldConditionTerm::address_equal(u.address().clone(), v.address().clone()),
        true,
    );
    let equality = OldConditionTerm::PointerEqual(Box::new(u.clone()), Box::new(v.clone()));
    assert_ne!(addresses.decide(&equality), Some(true));
    let both = addresses
        .clone()
        .assume_condition(OldConditionTerm::uint64_equal(count(n), count(m)), true);
    assert_eq!(both.decide(&equality), Some(true));
}

/// Substituting a slice's count keeps its type: a `str` stays a `str`.
#[test]
fn substitution_keeps_a_slice_type() {
    let _session = VerificationSession::enter();
    let text = wide(960_050, 960_051).with_type(ProgramType::SlicePointer(SliceElement::Str));
    let mapped = text.map_pointers(Address::clone, |_| count(960_052));
    assert_eq!(mapped.len(), Some(&count(960_052)));
    assert_eq!(mapped.program_type(), text.program_type());
    let mapped = text
        .try_map_pointers(|address| Some(address.clone()), |_| Some(count(960_053)))
        .unwrap();
    assert_eq!(mapped.len(), Some(&count(960_053)));
    assert_eq!(mapped.program_type(), text.program_type());
    let respelled = text.map_addresses(Address::clone, |_| count(960_054));
    assert_eq!(respelled.program_type(), text.program_type());
}

/// Rebasing a pending allocation respells a slice's addresses in the
/// resolved block and keeps its count and type, as it keeps a bounds width.
#[test]
fn an_allocation_rebase_keeps_a_slice_count() {
    let _session = VerificationSession::enter();
    let base = Address::symbolic(Variable(960_060));
    let resolved = Address::new("heap:resolved-slice".into(), AddressOffset::constant(0));
    let s =
        Pointer::new(base.clone(), ProgramType::UInt8Pointer).with_element_count(count(960_061));
    let rebased = crate::kernel::eval::rebase_resolved_allocation(&s, &base, &resolved);
    assert_eq!(rebased.address(), &resolved);
    assert_eq!(rebased.len(), s.len());
    assert_eq!(rebased.program_type(), s.program_type());
}
