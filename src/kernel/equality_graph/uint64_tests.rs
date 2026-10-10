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
        Box::new(Bitvector32Term::PointerAddress(Box::new(parent.clone()))),
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

#[test]
fn wide_congruence_queries_do_not_scan_unrelated_equalities() {
    let mut previous = None;
    for size in [16_u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let p = Pointer::symbolic(Variable(940_001));
        let q = Pointer::symbolic(Variable(940_002));
        let a = Bitvector32Term::Variable(Variable(940_003));
        let b = Bitvector32Term::Variable(Variable(940_004));
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_uint64_equality(
                &Bitvector32Term::Variable(Variable(i)),
                &Bitvector32Term::Variable(Variable(i + 10_000)),
            );
        }
        graph.add_uint64_equality(&a, &packed(&b, &p));
        graph.add_equality(&p, &q);
        let (ok, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_uint64_equal(&a, &packed(&b, &q))
        });
        assert!(ok);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "unrelated facts changed query work at {size}"
            );
        }
        previous = Some(work);
    }
}
