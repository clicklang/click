//! A wide pointer's element count in the e-graph
//! (`design/rust-slice-values.md`, "Equality"): the count is one more
//! congruence operand of the pointer, and a pointer equality merges it.
use super::*;

pub(super) fn count(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}
pub(super) fn thin(id: u64) -> Pointer {
    Pointer::new(Address::symbolic(Variable(id)), ProgramType::UInt8Pointer)
}
pub(super) fn wide(pointer: u64, length: u64) -> Pointer {
    thin(pointer).with_element_count(count(length))
}
pub(super) fn complete_equal(a: &Pointer, b: &Pointer) -> OldConditionTerm {
    OldConditionTerm::PointerEqual(Box::new(a.clone()), Box::new(b.clone()))
}

#[test]
fn equal_counts_make_equal_wide_pointers() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let (s, t) = (wide(950_001, 950_010), wide(950_001, 950_011));
    assert!(!graph.knows_condition(&complete_equal(&s, &t), true));
    assert!(!graph.knows_condition(&complete_equal(&s, &thin(950_001)), true));
    graph.add_uint64_equality(&count(950_010), &count(950_011));
    assert!(graph.knows_condition(&complete_equal(&s, &t), true));
    assert!(!graph.knows_condition(&complete_equal(&s, &thin(950_001)), true));
    assert!(!graph.knows_condition(&complete_equal(&s, &wide(950_002, 950_011)), true));
}

#[test]
fn wide_pointer_equality_merges_the_counts() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let (s, t) = (wide(950_021, 950_030), wide(950_022, 950_031));
    assert!(!graph.are_uint64_equal(&count(950_030), &count(950_031)));
    graph.add_pointer_equality(&s, &t);
    assert!(graph.are_uint64_equal(&count(950_030), &count(950_031)));
    assert!(graph.are_equal(s.address(), t.address()));
    assert!(graph.provenance_equal(s.provenance(), t.provenance()));
    assert!(graph.knows_condition(&complete_equal(&s, &t), true));
    // The thin parts are equal too: congruence on the remaining operands.
    assert!(graph.knows_condition(&complete_equal(&s.as_ptr(), &t.as_ptr()), true));
}

/// `s == t` on wide pointers lowers to the complete equality, never to an
/// address equality that would drop the counts, and an assumed one gives
/// `s.len() == t.len()`.
#[test]
fn assumed_wide_pointer_equality_gives_count_equality() {
    let _session = crate::kernel::VerificationSession::enter();
    let (s, t) = (wide(950_041, 950_050), wide(950_041, 950_051));
    let condition = OldConditionTerm::pointer_equal(s.clone(), t.clone());
    assert!(
        matches!(&condition, OldConditionTerm::PointerEqual(..)),
        "{condition:?}"
    );
    // Their thin parts are one pointer, whose equality reduces as before.
    assert!(!matches!(
        OldConditionTerm::pointer_equal(s.as_ptr(), t.as_ptr()),
        OldConditionTerm::PointerEqual(..)
    ));
    assert!(matches!(
        OldConditionTerm::logical_pointer_equal(s.clone(), s.clone()),
        OldConditionTerm::PointerEqual(..)
    ));
    assert!(condition.pointer_offset_sides().is_none());
    let kernel = crate::kernel::KernelTerm::pointer_equal([s.shared().clone(), t.shared().clone()]);
    assert!(matches!(
        kernel.node(),
        crate::kernel::KernelTermNode::PointerEqual(_)
    ));
    let context = PureFactContext::new();
    assert!(
        !context
            .equality_graph
            .are_uint64_equal(&count(950_050), &count(950_051))
    );
    let context = context.assume_condition(condition, true);
    assert!(
        context
            .equality_graph
            .are_uint64_equal(&count(950_050), &count(950_051))
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/wide_pointer_tests.rs");
}
