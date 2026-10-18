use super::*;
use crate::kernel::VerificationSession;

fn word(memory: &SharedCMemory, pointer: &Pointer, bytes: u32) -> Bitvector32Term {
    Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        LoadKind::Bits64,
        bytes,
    ))
}
fn packed(value: &Bitvector32Term, parent: &Pointer) -> Bitvector32Term {
    Bitvector32Term::UInt64Add(
        Box::new(Bitvector32Term::PointerAddress(
            Box::new(parent.clone()),
            crate::kernel::AddressObjectClass::NONE,
        )),
        Box::new(Bitvector32Term::UInt64BitwiseAnd(
            Box::new(value.clone()),
            Box::new(Bitvector32Term::UInt64Constant(1)),
        )),
    )
}
fn fact(a: Bitvector32Term, b: Bitvector32Term) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::uint64_equal(a, b), true)
}
fn alias(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(ConditionTerm::pointer_equal(a.clone(), b.clone()), true)
}
fn proved(context: &PureFactContext, goal: &Proposition) -> bool {
    crate::kernel::reasoning::required_obligation_is_exactly_discharged(context, goal)
}

fn raw_address(pointer: &Pointer) -> Bitvector32Term {
    // Deliberately bypass the surface constructor's address cancellation.
    Bitvector32Term::PointerAddress(Box::new(pointer.clone()), AddressObjectClass::NONE)
}

#[test]
fn integer_address_coordinates_join_word_classes_and_follow_scoped_equalities() {
    let _session = VerificationSession::enter();
    let bits = Bitvector32Term::Variable(Variable(960_001));
    let pointer = Pointer::symbolic(Variable(960_002));
    let decoded = Pointer::integer_address(bits.clone());
    let equation = fact(bits.clone(), raw_address(&pointer));
    let goal = Proposition::ConditionIs(
        ConditionTerm::uint64_equal(raw_address(&decoded), raw_address(&pointer)),
        true,
    );
    let base = PureFactContext::new();
    // Register the constructor before the premise, exercising a late merge.
    assert!(
        base.equality_graph
            .are_uint64_equal(&raw_address(&decoded), &bits)
    );
    assert!(!base.contains_known(&goal));
    let child = base.clone().assume_proposition(equation.clone());
    assert!(child.contains_known(&goal));
    assert!(
        child
            .equality_graph
            .are_uint64_equal(&raw_address(&decoded), &raw_address(&pointer))
    );
    assert!(!base.contains_known(&goal));
    assert!(!child.without_exact_fact(&equation).contains_known(&goal));
    assert!(!child.restricted_to_facts(&[], &[]).contains_known(&goal));
    let left = CPointerValue::new(decoded.clone(), CType::Int32Pointer);
    let right = CPointerValue::new(pointer.clone(), CType::Int32Pointer);
    // A cast that already carries the exact original domain can compare its
    // numeric coordinates. A bare address name cannot manufacture that domain.
    let original_domain = right.clone().with_address(decoded.clone());
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(
            Box::new(original_domain.clone()),
            Box::new(right.clone())
        ),
        true,
    )));
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(original_domain, right.clone()),
        true,
    )));
    assert!(!child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_equal(decoded, pointer),
        true,
    )));
    assert!(!child.pointer_designations_match(&left, &right));
    assert!(!child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(left, right),
        true,
    )));
}

#[test]
fn integer_address_definition_preserves_byte_displacements_and_load_snapshots() {
    let _session = VerificationSession::enter();
    let bits = Bitvector32Term::Variable(Variable(960_003));
    let decoded = Pointer::integer_address(bits.clone());
    let shifted = Pointer {
        block: decoded.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let sum = Bitvector32Term::uint64_add(bits.clone(), Bitvector32Term::UInt64Constant(8));
    let graph = EqualityGraph::default();
    assert!(graph.are_uint64_equal(&raw_address(&shifted), &sum));
    assert!(!graph.are_uint64_equal(&raw_address(&shifted), &bits));
    // Equal numeric addresses connect compatible reads, not snapshot identity.
    let memory = intern_c_memory(CMemory::new().with_block("coordinates", 32));
    let pointer = Pointer {
        block: "coordinates".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let after = intern_c_memory(memory.memory().clone().store(
        pointer.clone(),
        CValue::UInt64(Bitvector32Term::UInt64Constant(19)),
    ));
    let mut graph = graph;
    assert!(!graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&memory, &pointer, 8)));
    graph.add_uint64_equality(&bits, &raw_address(&pointer));
    assert!(graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&memory, &pointer, 8)));
    assert!(!graph.are_uint64_equal(&word(&memory, &decoded, 8), &word(&after, &pointer, 8)));
}

#[test]
fn equal_integer_address_words_do_not_merge_pointer_names_or_domains() {
    let _session = VerificationSession::enter();
    let a = Bitvector32Term::Variable(Variable(960_005));
    let b = Bitvector32Term::Variable(Variable(960_006));
    let p = Pointer::integer_address(a.clone());
    let q = Pointer::integer_address(b.clone());
    let mut context = PureFactContext::new();
    assert!(
        !context
            .equality_graph
            .are_uint64_equal(&raw_address(&p), &raw_address(&q))
    );
    context = context.assume_proposition(fact(a, b));
    assert!(
        context
            .equality_graph
            .are_uint64_equal(&raw_address(&p), &raw_address(&q))
    );
    assert!(!context.equality_graph.are_equal(&p, &q));
    let p = CPointerValue::new(p, CType::Int32Pointer);
    let q = CPointerValue::new(q, CType::Int32Pointer);
    assert!(!context.pointer_designations_match(&p, &q));
    assert!(!context.contains_known(&Proposition::ConditionIs(
        ConditionTerm::pointer_value_equal(p, q),
        true,
    )));
}

#[test]
fn wide_read_and_packed_word_congruence_compose_early_and_late() {
    let _session = VerificationSession::enter();
    let memory = intern_c_memory(CMemory::new().with_block("wide", 128));
    let zid = Pointer::symbolic(Variable(910_001));
    let sid = Pointer::symbolic(Variable(910_002));
    let p = Pointer::loaded_value(&memory, &Pointer::symbolic(Variable(910_003)));
    let q = Pointer::loaded_value(&memory, &Pointer::symbolic(Variable(910_004)));
    let v = word(&memory, &zid, 8);
    let a = word(&memory, &p, 8);
    let premise = fact(v.clone(), packed(&v, &sid));
    let goal = fact(a.clone(), packed(&a, &q));
    for early in [false, true] {
        let mut context = PureFactContext::new().defer_non_exact_condition_reasoning();
        if early {
            context = context
                .assume_proposition(alias(&p, &zid))
                .assume_proposition(alias(&q, &sid));
        }
        context = context.assume_proposition(premise.clone());
        if !early {
            assert!(!proved(&context, &goal));
            context = context.assume_proposition(alias(&p, &zid));
            assert!(proved(&context, &fact(a.clone(), v.clone())));
            assert!(!proved(&context, &goal), "parent alias is necessary");
            context = context.assume_proposition(alias(&q, &sid));
        }
        assert!(proved(&context, &goal));
        assert!(!proved(&context.without_exact_fact(&premise), &goal));
        for missing in [alias(&p, &zid), alias(&q, &sid)] {
            assert!(!proved(&context.without_exact_fact(&missing), &goal));
        }
        assert!(!proved(&context.restricted_to_facts(&[], &[]), &goal));
        assert!(!proved(
            &context
                .clone()
                .assume_condition(ConditionTerm::pointer_equal(q.clone(), sid.clone()), false),
            &goal
        ));
        // Cached closure results must not survive a weakened sibling context.
        assert!(proved(&context, &goal));
    }
}

#[test]
fn wide_reads_preserve_snapshot_width_and_value_sort() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("wide", 128));
    let p = Pointer::symbolic(Variable(920_001));
    let q = Pointer::symbolic(Variable(920_002));
    let after = intern_c_memory(before.memory().clone().store(
        p.clone(),
        CValue::UInt64(Bitvector32Term::UInt64Constant(9)),
    ));
    let a = word(&before, &p, 8);
    let b = word(&before, &q, 8);
    let mut graph = EqualityGraph::default();
    let sibling = graph.clone();
    graph.add_equality(&p, &q);
    assert!(graph.are_uint64_equal(&a, &b));
    assert!(!sibling.are_uint64_equal(&a, &b));
    assert!(!graph.are_uint64_equal(&a, &word(&after, &q, 8)));
    let narrow = Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        &before,
        &q,
        LoadKind::Bits32,
        4,
    ));
    assert!(!graph.are_uint64_equal(&a, &narrow));
    let x = Bitvector32Term::Variable(Variable(920_010));
    let y = Bitvector32Term::Variable(Variable(920_011));
    graph.add_int32_equality(&x, &y);
    assert!(!graph.are_uint64_equal(&x, &y));
    let mut wide_only = EqualityGraph::default();
    wide_only.add_uint64_equality(&x, &y);
    assert!(!wide_only.are_int32_equal(&x, &y));
    // Equality of applications never implies equality of their operands.
    let r = Pointer::symbolic(Variable(920_003));
    wide_only.add_uint64_equality(&packed(&x, &p), &packed(&x, &r));
    assert!(!wide_only.are_equal(&p, &r));
}

#[test]
fn wide_equality_inputs_reconstruct_in_derived_graphs() {
    let _session = VerificationSession::enter();
    let p = Pointer::symbolic(Variable(930_001));
    let q = Pointer::symbolic(Variable(930_002));
    let a = Bitvector32Term::Variable(Variable(930_003));
    let b = Bitvector32Term::Variable(Variable(930_004));
    let mut graph = EqualityGraph::default();
    let mut derived = graph.input_root();
    graph.add_uint64_equality(&a, &packed(&b, &p));
    graph.add_equality(&p, &q);
    assert!(derived.append_inputs_from(&graph));
    assert!(derived.are_uint64_equal(&a, &packed(&b, &q)));
    assert!(!graph.input_root().are_uint64_equal(&a, &packed(&b, &q)));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/uint64_tests.rs");
}
