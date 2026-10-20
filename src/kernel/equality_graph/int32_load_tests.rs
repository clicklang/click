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

#[test]
fn reads_at_equal_addresses_are_equal_without_equal_pointers() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_c_memory(
        CMemory::new()
            .with_block("left", 64)
            .with_block("right", 64),
    );
    let at = |block: &str, bytes: i64| Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(bytes),
    };
    let address_of = |pointer: Pointer| Bitvector32Term::pointer_address(pointer);
    let after = intern_c_memory(
        memory
            .memory()
            .clone()
            .store(at("left", 8), CValue::Int32(Bitvector32Term::Constant(9))),
    );
    for field in [0, 8] {
        let left = load(&memory, &at("left", field), 4);
        let right = load(&memory, &at("right", field), 4);
        let changed = load(&after, &at("right", field), 4);
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_int32_equal(&left, &right));
        graph.add_uint64_equality(&address_of(at("left", 0)), &address_of(at("right", 0)));
        assert!(graph.are_int32_equal(&left, &right), "field at {field}");
        assert!(!graph.are_int32_equal(&left, &changed));
        assert!(!graph.are_equal(&at("left", field), &at("right", field)));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/int32_load_tests.rs");
}

#[test]
fn native_pointer_aliases_reach_named_nested_pointer_reads() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let field = address(940_061);
    let arena = Pointer::symbolic(Variable(940_062));
    let native = Pointer::loaded_value(&memory, &field);
    let mut graph = EqualityGraph::default();
    graph.add_equality(&native, &arena);
    let named_read = |address: &Pointer| {
        let value = Pointer::loaded(address.block.clone(), load(&memory, address, 8), 4);
        graph.register_pointer_read_definition(&value, &memory, address);
        value
    };
    let named_arena = named_read(&field);
    let direct = named_read(&arena.clone().offset_by_bytes(8));
    let indirect = named_read(&named_arena.offset_by_bytes(8));
    let direct_cell = direct.clone().offset_by_elements(var(940_063), 4);
    let indirect_cell = indirect.clone().offset_by_elements(var(940_063), 4);
    let scalar_left = load(&memory, &direct_cell, 4);
    let scalar_right = load(&memory, &indirect_cell, 4);
    assert!(graph.are_int32_equal(&scalar_left, &scalar_right));
    let other_cell = indirect.clone().offset_by_elements(var(940_064), 4);
    assert!(!graph.are_int32_equal(&scalar_left, &load(&memory, &other_cell, 4)));
    let other_width = indirect.clone().offset_by_elements(var(940_063), 8);
    assert!(!graph.are_int32_equal(&scalar_left, &load(&memory, &other_width, 4)));
    let unrelated = EqualityGraph::default();
    assert!(!unrelated.are_int32_equal(&scalar_left, &scalar_right));
    assert!(graph.are_equal(&direct, &indirect));
    // The pointee width does not enter a read's identity: the same read
    // with another stride names the same pointer, and its displacement
    // still distinguishes it.
    let other_stride = Pointer::loaded(field.block.clone(), load(&memory, &field, 8), 8);
    assert_eq!(other_stride, named_arena);
    assert!(graph.are_equal(&other_stride, &arena));
    assert!(!graph.are_equal(&other_stride.offset_by_bytes(8), &arena));
    // A scalar-indexed address beside the same load is not the read.
    let scalar_indexed = field
        .clone()
        .offset_by_elements(load(&memory, &field, 8), 8);
    assert!(scalar_indexed.as_loaded_value().is_none());
    assert!(!graph.are_equal(&scalar_indexed, &arena));
}

#[test]
fn int32_load_congruence_connects_base_reads_to_early_and_late_zero_offsets() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let base = address(940_081);
    let offset = var(940_082);
    let direct = load(&memory, &base, 4);
    let indexed = load(&memory, &base.offset_by_elements(offset.clone(), 4), 4);
    for early in [false, true] {
        let mut graph = EqualityGraph::default();
        if early {
            graph.add_int32_equality(&offset, &Bitvector32Term::Constant(0));
        }
        graph.add_int32_equality(&direct, &var(940_083));
        graph.add_int32_equality(&indexed, &var(940_084));
        if !early {
            assert!(!graph.are_int32_equal(&var(940_083), &var(940_084)));
            graph.add_int32_equality(&offset, &Bitvector32Term::Constant(0));
        }
        assert!(
            graph.are_int32_equal(&var(940_083), &var(940_084)),
            "early={early}"
        );
    }
}

#[test]
fn a_late_zero_index_alias_transfers_an_admitted_read_order_and_withdraws() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let base = address(940_085);
    let index = var(940_086);
    let direct = load(&memory, &base, 4);
    let indexed = load(&memory, &base.offset_by_elements(index.clone(), 4), 4);
    let next = load(
        &memory,
        &base.offset_by_elements(Bitvector32Term::add(index.clone(), 1u32.into()), 4),
        4,
    );
    let known = ConditionTerm::signed_less_than(next.clone(), indexed);
    let target = ConditionTerm::signed_less_than(next, direct);
    let root = PureFactContext::new().assume_condition(known, true);
    assert_eq!(root.decide(&target), None);
    let zero = Proposition::ConditionIs(ConditionTerm::equal(index, 0u32.into()), true);
    let equal = root.assume_proposition(zero.clone());
    assert_eq!(equal.decide(&target), Some(true));
    assert_eq!(
        crate::kernel::reasoning::decide_with_facts(&equal, &ExecutionFacts::new(), &target),
        Some(true),
    );
    let withdrawn = equal.without_exact_fact(&zero);
    assert_eq!(withdrawn.decide(&target), None);
    assert_eq!(
        crate::kernel::reasoning::decide_with_facts(&withdrawn, &ExecutionFacts::new(), &target),
        None,
    );
}
