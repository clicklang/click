use super::*;
use std::collections::BTreeMap;
use std::sync::Arc;

fn model_type(name: &str, field: AlgebraicValueType) -> AlgebraicType {
    let nominal = AlgebraicValueType::Algebraic {
        name: name.into(),
        arguments: vec![],
    };
    let variants: Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Empty".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Node".into(),
            fields: vec![field],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: name.into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(nominal, variants)]))),
    }
}
fn variable(ty: &AlgebraicType, id: u64) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(id)),
    }
}
fn constructor(ty: &AlgebraicType, variant: &str, fields: Vec<AlgebraicValue>) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.into(),
            fields,
        },
    }
}
fn eq(a: &AlgebraicTerm, b: &AlgebraicTerm) -> Proposition {
    Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
}
fn condition(a: &AlgebraicTerm, b: &AlgebraicTerm, truth: bool) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::AlgebraicEqual(Box::new(a.clone()), Box::new(b.clone())),
        truth,
    )
}
fn scalar(id: u64) -> AlgebraicValue {
    AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(Variable(id))))
}

#[test]
fn algebraic_closure_connects_checked_aliases_in_both_orientations() {
    let ty = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let (a, b, c) = (variable(&ty, 1), variable(&ty, 2), variable(&ty, 3));
    let empty = constructor(&ty, "Empty", vec![]);
    let node = constructor(&ty, "Node", vec![scalar(4)]);
    for ctor in [&empty, &node] {
        for reverse in [false, true] {
            let alias = if reverse { eq(&b, &a) } else { eq(&a, &b) };
            let context = PureFactContext::new()
                .assume_proposition(alias)
                .assume_proposition(condition(&c, &b, true))
                .assume_proposition(eq(&c, ctor));
            assert!(context.contains_known(&eq(&a, ctor)));
            assert!(context.contains_known(&condition(ctor, &a, true)));
            let mut derived = context.equality_graph.input_root();
            assert!(derived.append_inputs_from(&context.equality_graph));
            assert!(derived.are_algebraic_equal(&a, ctor));
        }
    }
}

#[test]
fn algebraic_closure_preserves_types_constructors_payloads_and_argument_order() {
    let ty = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let same = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let other = model_type("Other", AlgebraicValueType::C(CType::Int32));
    let changed = model_type("Model", AlgebraicValueType::C(CType::UInt32));
    let a = variable(&ty, 10);
    let node = constructor(&ty, "Node", vec![scalar(11)]);
    let mut graph = EqualityGraph::default();
    graph.add_algebraic_equality(&a, &node);
    assert!(graph.are_algebraic_equal(&variable(&same, 10), &node));
    assert!(!graph.are_algebraic_equal(&variable(&other, 10), &node));
    assert!(!graph.are_algebraic_equal(&variable(&changed, 10), &node));
    assert!(!graph.are_algebraic_equal(&a, &constructor(&ty, "Empty", vec![])));
    assert!(!graph.are_algebraic_equal(&a, &constructor(&ty, "Node", vec![scalar(12)])));
    assert!(!graph.add_algebraic_equality(&variable(&other, 10), &a));
    assert!(!graph.add_algebraic_equality(&a, &constructor(&ty, "Node", vec![])));
    let f = |name: &str, args: Vec<PureFunctionArgument>| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::PureFunctionApplication {
            name: name.into(),
            arguments: args,
        },
    };
    let args = |x, y| {
        vec![
            PureFunctionArgument::Algebraic(x),
            PureFunctionArgument::Algebraic(y),
        ]
    };
    let b = variable(&ty, 13);
    assert!(!graph.are_algebraic_equal(
        &f("f", args(a.clone(), b.clone())),
        &f("f", args(b.clone(), a.clone()))
    ));
    assert!(!graph.are_algebraic_equal(
        &f("f", args(a.clone(), b.clone())),
        &f("g", args(a.clone(), b.clone()))
    ));
    graph.add_algebraic_equality(
        &f("f", args(a.clone(), b.clone())),
        &f("f", args(b.clone(), a.clone())),
    );
    assert!(!graph.are_algebraic_equal(&a, &b)); // no function injectivity
}

#[test]
fn algebraic_closure_propagates_late_model_and_scalar_merges_through_calls() {
    let ty = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let (a, b) = (variable(&ty, 20), variable(&ty, 21));
    let call = |v| Bitvector32Term::ClickFunctionApplication {
        name: "model_size".into(),
        arguments: vec![PureFunctionArgument::Algebraic(v)],
    };
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&call(a.clone()), &call(b.clone())));
    graph.add_algebraic_equality(&a, &b);
    assert!(graph.are_int32_equal(&call(a), &call(b)));
    let lhs = constructor(&ty, "Node", vec![scalar(22)]);
    let rhs = constructor(&ty, "Node", vec![scalar(23)]);
    assert!(!graph.are_algebraic_equal(&lhs, &rhs));
    graph.add_int32_equality(
        &Bitvector32Term::Variable(Variable(22)),
        &Bitvector32Term::Variable(Variable(23)),
    );
    assert!(graph.are_algebraic_equal(&lhs, &rhs));
}

#[test]
fn algebraic_closure_keeps_branch_scope_counted_support_and_withdrawal() {
    let ty = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let (a, b) = (variable(&ty, 30), variable(&ty, 31));
    let empty = constructor(&ty, "Empty", vec![]);
    let edge = eq(&a, &b);
    let ctor = eq(&b, &empty);
    let base = PureFactContext::new().assume_proposition(edge.clone());
    let branch = base.clone().assume_proposition(ctor.clone());
    assert!(!base.contains_known(&eq(&a, &empty)));
    assert!(branch.contains_known(&eq(&a, &empty)));
    assert!(
        !branch
            .without_exact_fact(&edge)
            .contains_known(&eq(&a, &empty))
    );
    assert!(
        !branch
            .without_exact_fact(&ctor)
            .contains_known(&eq(&a, &empty))
    );
    assert!(
        !branch
            .restricted_to_facts(&[], std::slice::from_ref(&edge))
            .contains_known(&eq(&a, &empty))
    );
    let duplicate = condition(&b, &a, true);
    let both = branch
        .assume_proposition(duplicate.clone())
        .without_exact_fact(&edge);
    assert!(both.contains_known(&eq(&a, &empty)));
    assert!(
        !both
            .without_exact_fact(&duplicate)
            .contains_known(&eq(&a, &empty))
    );
    let negative = base.assume_proposition(condition(&b, &empty, false));
    assert!(!negative.contains_known(&eq(&a, &empty)));
    assert!(negative.contains_known(&condition(&a, &empty, false)));
    assert!(!negative.contains_known(&condition(&a, &empty, true)));
}

#[test]
fn algebraic_closure_generic_arguments_and_constructor_field_order_remain_typed() {
    let mut ty = model_type("Pair", AlgebraicValueType::C(CType::Int32));
    ty.arguments = vec![AlgebraicValueType::C(CType::Int32)];
    ty.variants = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32); 2],
    }]
    .into();
    ty.schemas = Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        ty.value_type(),
        ty.variants.clone(),
    )])));
    let mut other = ty.clone();
    other.arguments = vec![AlgebraicValueType::C(CType::UInt32)];
    other.schemas = Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        other.value_type(),
        other.variants.clone(),
    )])));
    let mut graph = EqualityGraph::default();
    let a = constructor(&ty, "Node", vec![scalar(60), scalar(61)]);
    let b = constructor(&ty, "Node", vec![scalar(61), scalar(60)]);
    assert!(!graph.are_algebraic_equal(&a, &b));
    assert!(!graph.are_algebraic_equal(
        &a,
        &constructor(&other, "Node", vec![scalar(60), scalar(61)])
    ));
    graph.add_algebraic_equality(&variable(&ty, 62), &a);
    assert!(!graph.are_algebraic_equal(&variable(&other, 62), &a));
}

#[test]
fn algebraic_closure_pointer_payloads_share_the_existing_address_classes() {
    let ty = model_type("PointerModel", AlgebraicValueType::C(CType::Int32Pointer));
    let pointer = |name: &str| Pointer {
        block: name.into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let node = |p: Pointer, origin: Pointer| {
        constructor(
            &ty,
            "Node",
            vec![AlgebraicValue::C(CValue::Pointer(
                CPointerValue::new(p, CType::Int32Pointer).with_origin(origin),
            ))],
        )
    };
    let mut graph = EqualityGraph::default();
    graph.add_equality(&pointer("a"), &pointer("b"));
    assert!(!graph.are_algebraic_equal(
        &node(pointer("a"), pointer("a")),
        &node(pointer("b"), pointer("b"))
    ));
    assert!(graph.are_algebraic_equal(
        &node(pointer("a"), pointer("a")),
        &node(pointer("b"), pointer("a"))
    ));
}

#[test]
fn algebraic_closure_retains_each_schema_allocation_behind_a_memo_key() {
    let first = model_type("Model", AlgebraicValueType::C(CType::Int32));
    let second = model_type("Model", AlgebraicValueType::C(CType::Int32));
    assert!(!Arc::ptr_eq(&first.variants, &second.variants));
    let weak = Arc::downgrade(&second.variants);
    let graph = EqualityGraph::default();
    assert!(graph.are_algebraic_equal(&variable(&first, 70), &variable(&second, 70)));
    drop(second);
    // Interning equal types may retain only the first allocation. The memo
    // must independently retain the second so its address cannot be reused
    // for a different schema while the key remains live.
    assert!(weak.upgrade().is_some());
    drop(graph);
    assert!(weak.upgrade().is_none());
}

#[test]
fn scalar_conflicts_follow_model_congruence_and_withdrawn_support() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("ConflictModel", AlgebraicValueType::C(CType::Int32));
    let (a, b) = (variable(&ty, 900), variable(&ty, 901));
    let getter = |v| Bitvector32Term::ClickFunctionApplication {
        name: "pending".into(),
        arguments: vec![PureFunctionArgument::Algebraic(v)],
    };
    let value = |v, n| {
        Proposition::ConditionIs(
            ConditionTerm::equal(getter(v), Bitvector32Term::Constant(n)),
            true,
        )
    };
    let first = value(a.clone(), 1);
    let second = value(b.clone(), 0);
    let edge = eq(&a, &b);
    let base = PureFactContext::new()
        .assume_proposition(first)
        .assume_proposition(second.clone());
    assert!(!base.equality_graph.has_scalar_constant_conflict());
    assert!(!base.is_inconsistent());
    let child = base.clone().assume_proposition(edge.clone());
    assert!(child.contains_known(&value(a.clone(), 0)));
    assert!(child.equality_graph.has_scalar_constant_conflict());
    assert!(child.is_inconsistent());
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true
    )));
    assert!(!base.equality_graph.has_scalar_constant_conflict());
    for weakened in [
        child.without_exact_fact(&edge),
        child.without_exact_fact(&second),
        child.restricted_to_facts(&[], std::slice::from_ref(&edge)),
    ] {
        assert!(!weakened.equality_graph.has_scalar_constant_conflict());
        assert!(!weakened.is_inconsistent());
    }
    let duplicate = condition(&b, &a, true);
    let still_supported = child
        .assume_proposition(duplicate.clone())
        .without_exact_fact(&edge);
    assert!(
        still_supported
            .equality_graph
            .has_scalar_constant_conflict()
    );
    assert!(
        !still_supported
            .without_exact_fact(&duplicate)
            .equality_graph
            .has_scalar_constant_conflict()
    );
}

#[test]
fn scalar_constant_conflicts_preserve_machine_widths() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let x = Bitvector32Term::Variable(Variable(700));
    graph.add_int32_equality(&x, &Bitvector32Term::Constant(0));
    graph.add_uint64_equality(&x, &Bitvector32Term::UInt64Constant(1));
    assert!(!graph.has_scalar_constant_conflict());
    graph.add_uint64_equality(&x, &Bitvector32Term::UInt64Constant(0));
    assert!(graph.has_scalar_constant_conflict());
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&Bitvector32Term::Constant(0), &Bitvector32Term::Constant(1));
    assert!(graph.has_scalar_constant_conflict());
}

#[test]
fn scalar_read_conflicts_require_the_same_snapshot() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new().with_block("cell", 4).store(
        p.clone(),
        CValue::Int32(Bitvector32Term::Variable(Variable(500))),
    );
    let after = before.clone().store(
        p.clone(),
        CValue::Int32(Bitvector32Term::Variable(Variable(501))),
    );
    let memory = crate::kernel::intern_c_memory(before);
    let changed = crate::kernel::intern_c_memory(after);
    let read = |memory: crate::kernel::SharedCMemory| {
        Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &p,
            crate::kernel::LoadKind::Bits32,
            4,
            &memory,
        ))
    };
    let value = |term, n| {
        Proposition::ConditionIs(
            ConditionTerm::equal(term, Bitvector32Term::Constant(n)),
            true,
        )
    };
    for (right_memory, conflict) in [(memory.clone(), true), (changed, false)] {
        let context = PureFactContext::new()
            .assume_proposition(value(read(memory.clone()), 0))
            .assume_proposition(value(read(right_memory), 1));
        assert_eq!(
            context.equality_graph.has_scalar_constant_conflict(),
            conflict
        );
        assert_eq!(context.is_inconsistent(), conflict);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/algebraic_tests.rs");
}
