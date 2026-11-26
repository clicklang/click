use super::*;
use crate::kernel::VerificationSession;

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> OldAddress {
    OldAddress {
        base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: OldAddressOffset::Constant(0).into(),
    }
}
fn word(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}
fn argument(id: u64) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::Int32(word(id)))
}
fn pointer_argument(p: OldAddress) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::Pointer(OldPointer::new(
        p,
        ProgramType::Int32Pointer,
    )))
}
fn equal_pointer_arguments(graph: &mut EqualityGraph, p: &OldAddress, q: &OldAddress) {
    graph.add_pointer_equality(
        &OldPointer::new(p.clone(), ProgramType::Int32Pointer),
        &OldPointer::new(q.clone(), ProgramType::Int32Pointer),
    );
}

fn equal(a: &OldAddress, b: &OldAddress) -> Proposition {
    Proposition::condition_is(
        OldConditionTerm::AddressEqual(Box::new(a.clone()), Box::new(b.clone())),
        true,
    )
}

#[test]
fn pointer_calls_follow_late_model_aliases_and_displaced_addresses() {
    let _session = VerificationSession::enter();
    let ty = super::algebraic_tests::model_type(
        "Handle",
        AlgebraicValueType::Program(ProgramType::Int32Pointer),
    );
    let a = super::algebraic_tests::variable(&ty, 10);
    let b = super::algebraic_tests::variable(&ty, 11);
    let f = |x| call("handle", vec![PureFunctionArgument::Algebraic(x)]);
    let (left, right) = (f(a.clone()), f(b.clone()));
    let mut graph = EqualityGraph::default();
    let shifted = |p: &OldAddress| OldAddress {
        base: p.base.clone(),
        offset: OldAddressOffset::Constant(8).into(),
    };
    assert!(!graph.are_equal(&shifted(&left), &shifted(&right)));
    graph.add_algebraic_equality(&a, &b);
    assert!(graph.are_equal(&left, &right));
    assert!(graph.are_equal(&shifted(&left), &shifted(&right)));
    assert!(!graph.are_equal(&left, &shifted(&right)));
    assert!(!graph.are_equal(
        &left,
        &call("other", vec![PureFunctionArgument::Algebraic(b)])
    ));
}

#[test]
fn pointer_calls_keep_sorts_order_states_and_noninjectivity() {
    let _session = VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let p = OldAddress::symbolic(Variable(30));
    let q = OldAddress::symbolic(Variable(31));
    let memory = SymbolicMemory::new().with_block(p.base.clone(), 4);
    let changed = memory
        .clone()
        .store(p.clone(), ProgramValue::Int32(word(32)));
    let array = |memory: &SymbolicMemory, pointer, element_type| PureFunctionArgument::ArrayRef {
        point: crate::kernel::ProgramPoint::of_memory(memory),
        pointer: ProgramValue::Pointer(OldPointer::new(pointer, ProgramType::Int32Pointer)),
        element_type,
    };
    let a = call(
        "select",
        vec![array(&memory, p.clone(), ProgramType::Int32)],
    );
    let b = call(
        "select",
        vec![array(&memory, q.clone(), ProgramType::Int32)],
    );
    assert!(!graph.are_equal(&a, &b));
    graph.add_equality(&p, &q);
    assert!(!graph.are_equal(&a, &b));
    equal_pointer_arguments(&mut graph, &p, &q);
    assert!(graph.are_equal(&a, &b));
    assert!(!graph.are_equal(
        &a,
        &call(
            "select",
            vec![array(&changed, q.clone(), ProgramType::Int32)]
        )
    ));
    assert!(!graph.are_equal(
        &a,
        &call("select", vec![array(&memory, q, ProgramType::UInt32)])
    ));
    let a = call("pair", vec![argument(33), argument(34)]);
    let b = call("pair", vec![argument(34), argument(33)]);
    assert!(!graph.are_equal(&a, &b));
    assert!(!graph.are_equal(
        &call("typed", vec![argument(33)]),
        &call(
            "typed",
            vec![PureFunctionArgument::Value(ProgramValue::UInt32(word(33)))]
        )
    ));
    assert!(!graph.are_equal(&a, &call("pair", vec![argument(33)])));
    graph.add_equality(&a, &b);
    assert!(!graph.are_int32_equal(&word(33), &word(34)));
}

#[test]
fn nested_pointer_calls_feed_scalar_calls_and_checked_reads() {
    let _session = VerificationSession::enter();
    let (p, q) = (
        OldAddress::symbolic(Variable(40)),
        OldAddress::symbolic(Variable(41)),
    );
    let build = |mut p: OldAddress| {
        for _ in 0..12 {
            p = call("next", vec![pointer_argument(p)]);
        }
        p
    };
    let (a, b) = (build(p.clone()), build(q.clone()));
    let scalar = |p| OldMachineTerm::ClickFunctionApplication {
        name: "count".into(),
        arguments: vec![pointer_argument(p)],
    };
    let memory = intern_memory(SymbolicMemory::new());
    let read = |p| {
        OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &p,
            LoadKind::Int32,
            4,
        ))
    };
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&scalar(a.clone()), &scalar(b.clone())));
    assert!(!graph.are_int32_equal(&read(a.clone()), &read(b.clone())));
    graph.add_equality(&p, &q);
    assert!(!graph.are_equal(&a, &b));
    equal_pointer_arguments(&mut graph, &p, &q);
    assert!(graph.are_equal(&a, &b));
    assert!(graph.are_int32_equal(&scalar(a.clone()), &scalar(b.clone())));
    assert!(graph.are_int32_equal(&read(a), &read(b)));
}

#[test]
fn pointer_call_evidence_stays_scoped() {
    let _session = VerificationSession::enter();
    let (a, b) = (
        call("get", vec![argument(50)]),
        call("get", vec![argument(51)]),
    );
    let p = OldAddress::symbolic(Variable(52));
    let premise = Proposition::condition_is(OldConditionTerm::equal(word(50), word(51)), true);
    let held = equal(&p, &a);
    let goal = equal(&p, &b);
    let base = PureFactContext::new().assume_proposition(held.clone());
    assert!(!base.contains_known(&goal));
    let child = base.clone().assume_proposition(premise.clone());
    assert!(child.contains_known(&goal));
    assert!(!base.contains_known(&goal));
    assert!(
        !PureFactContext::new()
            .assume_proposition(premise)
            .contains_known(&goal)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/pointer_call_tests.rs");
}

#[test]
fn pointer_call_address_equality_does_not_merge_result_domains() {
    let _session = VerificationSession::enter();
    let a = call("left", vec![argument(61)]);
    let b = call("right", vec![argument(61)]);
    let left = OldPointer::new(a.clone(), ProgramType::Int32Pointer);
    let right = OldPointer::new(b.clone(), ProgramType::Int32Pointer);
    let context = PureFactContext::new().assume_proposition(equal(&a, &b));
    assert!(!context.pointer_provenance_match(&left, &right));
    let complete = context.clone().assume_condition(
        OldConditionTerm::pointer_equal(left.clone(), right.clone()),
        true,
    );
    assert!(complete.pointer_provenance_match(&left, &right));
    assert!(!context.pointer_provenance_match(&left, &right));
}
