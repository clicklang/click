use super::*;
use crate::kernel::VerificationSession;

fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}

fn eq(left: &Bitvector32Term, right: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::equal(left.clone(), right.clone())
}

#[test]
fn int32_equality_is_transitive_symmetric_and_branch_local() {
    let (a, b, c) = (var(1), var(2), var(3));
    let mut parent = EqualityGraph::default();
    parent.add_int32_equality(&a, &b);
    let sibling = parent.clone();
    let mut branch = parent.clone();
    assert!(!branch.are_int32_equal(&a, &c));
    branch.add_int32_equality(&b, &c);
    assert!(branch.are_int32_equal(&c, &a));
    assert!(branch.are_int32_equal(&a, &a));
    assert!(!parent.are_int32_equal(&a, &c));
    assert!(!sibling.are_int32_equal(&a, &c));
    assert!(!branch.add_int32_equality(&c, &a));
}

#[test]
fn int32_classes_are_typed_and_only_supported_operators_have_congruence() {
    let (a, b) = (var(1), var(2));
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&a, &b);
    assert!(!graph.are_offsets_equal(
        &PointerOffsetTerm::Variable(Variable(1)),
        &PointerOffsetTerm::Variable(Variable(2)),
    ));
    assert!(!graph.are_equal(
        &Pointer::symbolic(Variable(1)),
        &Pointer::symbolic(Variable(2))
    ));
    assert!(graph.are_offsets_equal(
        &PointerOffsetTerm::scale_int32(a.clone(), 4),
        &PointerOffsetTerm::scale_int32(b.clone(), 4),
    ));
    let plus_one =
        |value| Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
    assert!(graph.are_int32_equal(&plus_one(a.clone()), &plus_one(b.clone())));
    let minus_one =
        |value| Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
    assert!(!graph.are_int32_equal(&minus_one(a), &minus_one(b)));
    graph.add_offset_equality(
        &PointerOffsetTerm::Variable(Variable(3)),
        &PointerOffsetTerm::Variable(Variable(4)),
    );
    assert!(!graph.are_int32_equal(&var(3), &var(4)));
    assert!(!graph.are_int32_equal(&Bitvector32Term::Constant(0), &Bitvector32Term::Constant(1)));
}

#[test]
fn int32_withdrawal_restriction_and_replacement_keep_only_supported_edges() {
    let (a, b, c) = (var(10), var(11), var(12));
    let ab = eq(&a, &b);
    let bc = eq(&b, &c);
    let offset = |i| PointerOffsetTerm::Variable(Variable(i));
    let pq = ConditionTerm::pointer_equal(
        Pointer::symbolic(Variable(20)),
        Pointer::symbolic(Variable(21)),
    );
    let xy = ConditionTerm::pointer_offset_equal(offset(30), offset(31));
    let context = PureFactContext::new()
        .assume_condition(ab.clone(), true)
        .assume_condition(bc.clone(), true)
        .assume_condition(pq.clone(), true)
        .assume_condition(xy.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let weakened = context.without_exact_fact(&Proposition::ConditionIs(bc.clone(), true));
    assert!(!weakened.equality_graph.are_int32_equal(&a, &c));
    assert!(weakened.equality_graph.are_int32_equal(&a, &b));
    assert!(
        weakened
            .equality_graph
            .are_offsets_equal(&offset(30), &offset(31))
    );
    assert!(weakened.equality_graph.are_equal(
        &Pointer::symbolic(Variable(20)),
        &Pointer::symbolic(Variable(21))
    ));
    for fact in [pq, xy] {
        let weakened = context.without_exact_fact(&Proposition::ConditionIs(fact, true));
        assert!(weakened.equality_graph.are_int32_equal(&a, &c));
    }
    let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let replaced = context.clone().assume_condition(bc, false);
    assert!(!replaced.equality_graph.are_int32_equal(&a, &c));
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let reversed = context.clone().assume_condition(eq(&b, &a), true);
    let once = reversed.without_exact_fact(&Proposition::ConditionIs(eq(&a, &b), true));
    assert!(once.equality_graph.are_int32_equal(&a, &c));
    let twice = once.without_exact_fact(&Proposition::ConditionIs(eq(&b, &a), true));
    assert!(!twice.equality_graph.are_int32_equal(&a, &c));
}

#[test]
fn int32_load_identity_keeps_snapshots_and_exact_support_separate() {
    let _session = VerificationSession::enter();
    let before = intern_c_memory(CMemory::new().with_block("int32", 8));
    let pointer = Pointer::symbolic(Variable(40));
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let load = |memory: &SharedCMemory| {
        Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone()))
    };
    let named = Bitvector32Term::Variable(load_variable_for_cell_with_origin(
        &before, &pointer, 4, &before,
    ));
    let a = var(41);
    let context = PureFactContext::new()
        .assume_condition(eq(&load(&before), &a), true)
        .assume_condition(eq(&named, &a), true);
    assert!(context.equality_graph.are_int32_equal(&load(&before), &a));
    assert!(!context.equality_graph.are_int32_equal(&load(&after), &a));
    let scale = |value| PointerOffsetTerm::scale_int32(value, 4);
    assert!(
        context
            .equality_graph
            .are_offsets_equal(&scale(load(&before)), &scale(a.clone()))
    );
    assert!(
        !context
            .equality_graph
            .are_offsets_equal(&scale(load(&after)), &scale(a.clone()))
    );
    let sum = |value| Bitvector32Term::Add(Box::new(value), Box::new(var(42)));
    assert!(
        context
            .equality_graph
            .are_int32_equal(&sum(load(&before)), &sum(a.clone()))
    );
    assert!(
        !context
            .equality_graph
            .are_int32_equal(&sum(load(&after)), &sum(a.clone()))
    );
    let once = context.without_exact_fact(&Proposition::ConditionIs(eq(&load(&before), &a), true));
    assert!(once.equality_graph.are_int32_equal(&named, &a));
    let twice = once.without_exact_fact(&Proposition::ConditionIs(eq(&named, &a), true));
    assert!(!twice.equality_graph.are_int32_equal(&load(&before), &a));
}

#[test]
fn int32_context_insertion_and_forks_scale_with_indexed_work() {
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let ((context, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut context = PureFactContext::new();
                for i in 0..size {
                    context = context.assume_condition(eq(&var(i), &var(i + 1)), true);
                    assert!(context.equality_graph.are_int32_equal(&var(0), &var(i + 1)));
                }
                context
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work < 300 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1200 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let branch = context
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert!(
                    branch
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
                assert!(
                    !context
                        .equality_graph
                        .are_int32_equal(&var(0), &var(size + 1))
                );
            })
        });
        assert!(work < 300, "size={size}, fork work={work}");
        assert!(
            map_work < 1200 * logarithm,
            "size={size}, fork map work={map_work}"
        );
    }
}

#[test]
fn scalar_support_tracking_does_not_compare_unrelated_snapshot_contents_across_arenas() {
    fn sample(size: usize) -> (PureFactContext, usize) {
        std::thread::spawn(move || {
            let _session = VerificationSession::enter();
            let address = Pointer {
                block: "selected".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut memory = CMemory::new().with_block("selected", 4);
            for i in 0..size {
                memory = memory.with_block(format!("unrelated-{i}"), 4);
            }
            let memory = intern_c_memory(
                memory.store(address.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
            );
            let load = Bitvector32Term::MemoryLoad(memory, Box::new(address));
            crate::instrumentation::measure_deterministic_work(|| {
                PureFactContext::new()
                    .assume_condition(eq(&load, &Bitvector32Term::Constant(7)), true)
            })
        })
        .join()
        .expect("independent verification arena")
    }
    for size in [16, 64, 256, 1024] {
        // Retain the first context while admitting the same raw load shape in
        // another arena. Global raw-term interning used to compare the two
        // complete, independently allocated snapshots during the second insert.
        let (held, _) = sample(size);
        let (_, work) = sample(size);
        assert!(work < 100, "size={size}, second-arena work={work}");
        drop(held);
    }
}

#[test]
fn offset_premises_support_scalar_graph_edges_and_withdrawal() {
    let (a, b, c) = (var(70), var(71), var(72));
    let offset_eq = |left: Bitvector32Term, right: Bitvector32Term| {
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(left, 4),
            PointerOffsetTerm::scale_int32(right, 4),
        )
    };
    let scaled = offset_eq(a.clone(), b.clone());
    let direct = eq(&a, &b);
    let bc = eq(&b, &c);
    let context = PureFactContext::new()
        .assume_condition(scaled.clone(), true)
        .assume_condition(direct.clone(), true)
        .assume_condition(bc.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let without_direct = context.without_exact_fact(&Proposition::ConditionIs(direct, true));
    assert!(without_direct.equality_graph.are_int32_equal(&a, &c));
    let without_scaled =
        without_direct.without_exact_fact(&Proposition::ConditionIs(scaled.clone(), true));
    assert!(!without_scaled.equality_graph.are_int32_equal(&a, &c));
    assert!(without_scaled.equality_graph.are_int32_equal(&b, &c));
    let restricted = context.restricted_to_facts(&[(scaled, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let mut context = PureFactContext::new();
    for width in [0, 1, 8] {
        context = context.assume_condition(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(a.clone()),
                    byte_width: width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(b.clone()),
                    byte_width: width,
                },
            ),
            true,
        );
    }
    assert!(
        !context.equality_graph.are_int32_equal(&a, &b),
        "this ingress only translates four-byte element-index premises"
    );
}

#[test]
fn offset_premise_graph_insertion_and_forks_scale() {
    let add = |v| Bitvector32Term::Add(Box::new(v), Box::new(Bitvector32Term::Constant(1)));
    for size in [16u64, 64, 256, 1024] {
        let _session = VerificationSession::enter();
        let mut parent = PureFactContext::new();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    parent = parent.clone().assume_condition(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(var(i), 4),
                            PointerOffsetTerm::scale_int32(var(i + 1), 4),
                        ),
                        true,
                    );
                }
                for i in 1..=size {
                    assert!(
                        parent
                            .equality_graph
                            .are_int32_equal(&add(var(0)), &add(var(i)))
                    );
                }
                let branch = parent
                    .clone()
                    .assume_condition(eq(&var(size), &var(size + 1)), true);
                assert!(
                    branch
                        .equality_graph
                        .are_int32_equal(&add(var(0)), &add(var(size + 1)))
                );
                assert!(
                    !parent
                        .equality_graph
                        .are_int32_equal(&add(var(0)), &add(var(size + 1)))
                );
            })
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 150 * size as usize, "size={size}, work={work}");
        assert!(
            map_work < 1500 * size as usize * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}
