use super::*;
fn var(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(id))
}
fn address(id: u64) -> Pointer {
    Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::scale_int32(var(id), 4),
    }
}
fn load(memory: &SharedCMemory, pointer: &Pointer, bytes: u32) -> Bitvector32Term {
    Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        crate::kernel::LoadKind::Bits32,
        bytes,
    ))
}
fn memory() -> SharedCMemory {
    intern_c_memory(CMemory::new().with_block("array", 4096))
}

#[test]
fn int32_load_congruence_handles_early_and_late_offsets_and_scalar_parents() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let (left, right) = (load(&memory, &address(1), 4), load(&memory, &address(2), 4));
    let add = |v| Bitvector32Term::Add(Box::new(v), Box::new(var(3)));
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&var(1), &var(2));
        }
        graph.add_int32_equality(&add(left.clone()), &var(10));
        graph.add_int32_equality(&add(right.clone()), &var(11));
        if !early {
            assert!(!graph.are_int32_equal(&var(10), &var(11)));
            graph.add_int32_equality(&var(2), &var(1));
        }
        assert!(graph.are_int32_equal(&var(10), &var(11)));
    }
}

#[test]
fn shallow_scalar_decision_uses_only_registered_loads_in_one_snapshot() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let left = load(&before, &address(1), 4);
    let right = load(&before, &address(2), 4);
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(address(1), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let context =
        PureFactContext::new().assume_condition(ConditionTerm::equal(var(1), var(2)), true);
    assert_eq!(
        context.decide_bitvector_equality_shallow(&left, &right),
        Some(true)
    );
    assert_eq!(
        context.decide(&ConditionTerm::equal(left.clone(), right.clone())),
        Some(true)
    );
    assert_ne!(
        context.decide_bitvector_equality_shallow(&left, &changed),
        Some(true)
    );
    assert_ne!(
        context.decide(&ConditionTerm::equal(left, changed)),
        Some(true)
    );
}

#[test]
fn int32_load_congruence_keeps_snapshots_blocks_and_widths_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let after = intern_c_memory(
        memory
            .memory()
            .clone()
            .store(address(1), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let mut other_block = address(2);
    other_block.block = "other".into();
    let other = load(&memory, &other_block, 4);
    let narrow = load(&memory, &address(3), 2);
    let wide = load(&memory, &address(4), 8);
    let mut graph = EqualityGraph::default();
    for i in 2..=4 {
        graph.add_int32_equality(&var(1), &var(i));
    }
    assert!(graph.are_int32_equal(&left, &right));
    for unknown in [changed, other, narrow, wide] {
        assert!(!graph.are_int32_equal(&left, &unknown));
    }
    assert!(!graph.are_int32_equal(&left, &Bitvector32Term::Constant(9)));
}

#[test]
fn int32_load_congruence_is_branch_local_and_withdrawable() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let equality = ConditionTerm::equal(var(1), var(2));
    let parent = PureFactContext::new();
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    let sibling = parent.clone();
    let context = parent.clone().assume_condition(equality.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&left, &right));
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    assert!(!sibling.equality_graph.are_int32_equal(&left, &right));
    let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(equality, true));
    assert!(!withdrawn.equality_graph.are_int32_equal(&left, &right));
    assert!(
        !context
            .restricted_to_facts(&[], &[])
            .equality_graph
            .are_int32_equal(&left, &right)
    );
}

#[test]
fn int32_load_defining_snapshot_is_independent_of_live_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(address(1), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let left = Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Bits32,
        4,
        &before,
    ));
    crate::kernel::eval::begin_load_origin_epoch();
    // Change the mutable origin while retaining the exact defining snapshot.
    let renamed = Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Bits32,
        4,
        &after,
    ));
    assert_eq!(left, renamed);
    let right = load(&after, &address(2), 4);
    for term in [&left, &right] {
        let Bitvector32Term::Variable(variable) = term else {
            panic!("registered load")
        };
        assert_eq!(
            crate::kernel::eval::registered_load_origin_for_variable(variable)
                .unwrap()
                .0
                .arena_id(),
            after.arena_id()
        );
    }
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&var(1), &var(2));
    assert!(!graph.are_int32_equal(&left, &right));
    let raw = |m: &SharedCMemory| {
        Bitvector32Term::MemoryLoad(
            m.clone(),
            Box::new(address(1)),
            crate::kernel::LoadKind::Bits32,
        )
    };
    crate::kernel::eval::declare_load_access_width(&address(1), 4);
    assert!(!graph.are_int32_equal(&raw(&before), &raw(&after)));
}

#[test]
fn int32_load_registration_can_follow_a_later_width_declaration() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 2);
    let right = load(&memory, &address(2), 4);
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&var(1), &var(2));
    assert!(!graph.are_int32_equal(&left, &right));
    assert_eq!(left, load(&memory, &address(1), 4));
    assert!(graph.are_int32_equal(&left, &right));
}

#[test]
fn explicit_cross_snapshot_load_equality_composes_without_merging_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_c_memory(
        before
            .memory()
            .clone()
            .store(address(3), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    let old_i = load(&before, &address(1), 4);
    let new_i = load(&after, &address(1), 4);
    let old_j = load(&before, &address(2), 4);
    let new_j = load(&after, &address(2), 4);
    // This edge represents a separately checked transport conclusion. The
    // graph must compose it, but must not itself infer that a store is disjoint.
    let bridge = ConditionTerm::equal(old_i.clone(), new_i.clone());
    let indices = ConditionTerm::equal(var(1), var(2));
    let parent = PureFactContext::new().assume_condition(indices.clone(), true);
    assert!(parent.equality_graph.are_int32_equal(&old_i, &old_j));
    assert!(!parent.equality_graph.are_int32_equal(&old_j, &new_j));
    let sibling = parent.clone();
    let context = parent.clone().assume_condition(bridge.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&old_j, &new_j));
    assert!(!sibling.equality_graph.are_int32_equal(&old_j, &new_j));
    assert!(!context.equality_graph.are_int32_equal(
        &load(&before, &address(3), 4),
        &load(&after, &address(3), 4)
    ));
    let withdrawn = context.without_exact_fact(&Proposition::ConditionIs(bridge.clone(), true));
    assert!(!withdrawn.equality_graph.are_int32_equal(&old_j, &new_j));
    assert!(withdrawn.equality_graph.are_int32_equal(&old_i, &old_j));
    let restricted = context.restricted_to_facts(&[(bridge.clone(), true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&old_i, &new_i));
    assert!(!restricted.equality_graph.are_int32_equal(&old_j, &new_j));
    let reverse_order = PureFactContext::new()
        .assume_condition(bridge, true)
        .assume_condition(indices, true);
    assert!(reverse_order.equality_graph.are_int32_equal(&old_j, &new_j));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/int32_load_tests.rs");
}
