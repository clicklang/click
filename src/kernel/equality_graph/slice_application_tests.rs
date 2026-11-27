//! A slice-valued pure application's element count in the e-graph
//! (`design/rust-slice-values.md`, step 2b-iii-b-ii): `f(x).len()` is a
//! projection of the application's identity beside its provenance and
//! bounds, so the counts of applications to equal arguments are equal, and a
//! definitional unfolding `f(x) == body` joins both components with the
//! body's slice.
use super::wide_pointer_tests::{complete_equal, count, wide};
use super::*;

pub(super) fn argument(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

/// `name(x)` for the `int32` variable `x`.
pub(super) fn application(name: &str, id: u64) -> crate::kernel::SharedPureApplication {
    crate::kernel::SharedPureApplication::intern(
        name.into(),
        vec![crate::kernel::PureFunctionArgument::Value(
            ProgramValue::Int32(argument(id)),
        )],
    )
}

/// The `&[u8]` that `name(x)` returns.
pub(super) fn slice_of(name: &str, id: u64) -> Pointer {
    crate::kernel::spec::pure_slice_application_value(
        &application(name, id),
        crate::kernel::SliceElement::UInt8,
        ProgramType::SlicePointer(crate::kernel::SliceElement::UInt8),
    )
}

pub(super) fn count_of(name: &str, id: u64) -> OldMachineTerm {
    OldMachineTerm::pure_application_count(application(name, id))
}

#[test]
fn application_counts_are_congruent_on_their_arguments() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let (fx, fy, gx) = (
        count_of("bytes_of", 956_000),
        count_of("bytes_of", 956_001),
        count_of("other_bytes", 956_000),
    );
    assert!(graph.are_uint64_equal(&fx, &count_of("bytes_of", 956_000)));
    assert!(!graph.are_uint64_equal(&fx, &fy));
    assert!(!graph.are_uint64_equal(&fx, &gx));
    graph.add_int32_equality(&argument(956_000), &argument(956_001));
    assert!(graph.are_uint64_equal(&fx, &fy));
    assert!(!graph.are_uint64_equal(&fx, &gx));
    // The whole slices are congruent too: both components follow the one
    // argument equality.
    assert!(graph.knows_condition(
        &complete_equal(
            &slice_of("bytes_of", 956_000),
            &slice_of("bytes_of", 956_001)
        ),
        true
    ));
}

/// A count is never the integer application of the same name: that would
/// be another function of that name.
#[test]
fn an_application_count_is_not_an_integer_application() {
    let _session = crate::kernel::VerificationSession::enter();
    let graph = EqualityGraph::default();
    let integer = OldMachineTerm::ClickFunctionApplication {
        name: "bytes_of".into(),
        arguments: application("bytes_of", 956_010).arguments().to_vec(),
    };
    assert!(!graph.are_uint64_equal(&count_of("bytes_of", 956_010), &integer));
}

/// Unfolding `f(x) == body` at slice type is a complete pointer equality:
/// it joins the application's count with the body's count and its thin part
/// with the body's thin part, as stated directly or as an assumed fact.
#[test]
fn unfolding_a_slice_application_joins_both_components() {
    let _session = crate::kernel::VerificationSession::enter();
    let application = slice_of("bytes_of", 956_020);
    let body = wide(956_021, 956_022);
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_uint64_equal(application.len().unwrap(), &count(956_022)));
    graph.add_pointer_equality(&application, &body);
    assert!(graph.are_uint64_equal(application.len().unwrap(), &count(956_022)));
    assert!(graph.are_equal(application.address(), body.address()));
    assert!(graph.knows_condition(&complete_equal(&application, &body), true));

    let condition = OldConditionTerm::pointer_equal(application.clone(), body.clone());
    assert!(matches!(condition, OldConditionTerm::PointerEqual(..)));
    let context = PureFactContext::new().assume_condition(condition, true);
    assert!(
        context
            .equality_graph
            .are_uint64_equal(application.len().unwrap(), &count(956_022))
    );
    // Another application's count is untouched.
    assert!(
        !context
            .equality_graph
            .are_uint64_equal(&count_of("bytes_of", 956_023), &count(956_022))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/slice_application_tests.rs");
}
