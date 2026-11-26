use super::*;
use crate::kernel::MachineCastSpelling;
use crate::kernel::binary_node;
fn var(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}
fn address(id: u64) -> OldAddress {
    OldAddress {
        base: "array".into(),
        offset: OldAddressOffset::scale_int32(var(id), 4).into(),
    }
}
fn load(memory: &SharedMemory, pointer: &OldAddress, bytes: u32) -> OldMachineTerm {
    OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        pointer,
        crate::kernel::LoadKind::Int32,
        bytes,
    ))
}
fn memory() -> SharedMemory {
    intern_memory(SymbolicMemory::new().with_block("array", 4096))
}

#[test]
fn int32_load_congruence_handles_early_and_late_offsets_and_scalar_parents() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let (left, right) = (load(&memory, &address(1), 4), load(&memory, &address(2), 4));
    let add = |v| binary_node!(Int32, Add, Box::new(v), Box::new(var(3)));
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
fn shallow_scalar_decision_uses_only_registered_loads_in_one_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let left = load(&before, &address(1), 4);
    let right = load(&before, &address(2), 4);
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(OldMachineTerm::constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let context =
        PureFactContext::new().assume_condition(OldConditionTerm::equal(var(1), var(2)), true);
    assert_eq!(
        context.decide_bitvector_equality_shallow(&left, &right),
        Some(true)
    );
    assert_eq!(
        context.decide(&OldConditionTerm::equal(left.clone(), right.clone())),
        Some(true)
    );
    assert_ne!(
        context.decide_bitvector_equality_shallow(&left, &changed),
        Some(true)
    );
    assert_ne!(
        context.decide(&OldConditionTerm::equal(left, changed)),
        Some(true)
    );
}

#[test]
fn int32_load_congruence_keeps_states_blocks_and_widths_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let after = intern_memory(
        memory
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(OldMachineTerm::constant(9))),
    );
    let changed = load(&after, &address(2), 4);
    let mut other_block = address(2);
    other_block.base = "other".into();
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
    assert!(!graph.are_int32_equal(&left, &OldMachineTerm::constant(9)));
}

#[test]
fn int32_load_congruence_is_branch_local() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let left = load(&memory, &address(1), 4);
    let right = load(&memory, &address(2), 4);
    let equality = OldConditionTerm::equal(var(1), var(2));
    let parent = PureFactContext::new();
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    let sibling = parent.clone();
    let context = parent.clone().assume_condition(equality.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&left, &right));
    assert!(!parent.equality_graph.are_int32_equal(&left, &right));
    assert!(!sibling.equality_graph.are_int32_equal(&left, &right));
    assert!(
        !context
            .restricted_to_facts(&[], &[])
            .equality_graph
            .are_int32_equal(&left, &right)
    );
}

#[test]
fn int32_load_defining_state_is_independent_of_live_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(1), ProgramValue::Int32(OldMachineTerm::constant(9))),
    );
    let left = OldMachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Int32,
        4,
        &before,
    ));
    crate::kernel::eval::begin_load_origin_epoch();
    // Change the mutable origin while retaining the exact defining state.
    let renamed = OldMachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
        &before,
        &address(1),
        crate::kernel::LoadKind::Int32,
        4,
        &after,
    ));
    assert_eq!(left, renamed);
    let right = load(&after, &address(2), 4);
    for term in [&left, &right] {
        let OldMachineTerm::Variable(variable) = term else {
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
    let raw = |m: &SharedMemory| {
        OldMachineTerm::read_named(
            ProgramPoint::at(m),
            Box::new(address(1)),
            crate::kernel::LoadKind::Int32,
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
fn explicit_cross_state_load_equality_composes_without_merging_states() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let after = intern_memory(
        before
            .memory()
            .clone()
            .store(address(3), ProgramValue::Int32(OldMachineTerm::constant(9))),
    );
    let old_i = load(&before, &address(1), 4);
    let new_i = load(&after, &address(1), 4);
    let old_j = load(&before, &address(2), 4);
    let new_j = load(&after, &address(2), 4);
    // This edge represents a separately checked transport conclusion. The
    // graph must compose it, but must not itself infer that a store is disjoint.
    let bridge = OldConditionTerm::equal(old_i.clone(), new_i.clone());
    let indices = OldConditionTerm::equal(var(1), var(2));
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
    let memory = intern_memory(
        SymbolicMemory::new()
            .with_block("left", 64)
            .with_block("right", 64),
    );
    let at = |block: &str, bytes: i64| OldAddress {
        base: block.into(),
        offset: OldAddressOffset::Constant(bytes).into(),
    };
    let address_of = |pointer: OldAddress| OldMachineTerm::integer_address(pointer);
    let after = intern_memory(memory.memory().clone().store(
        at("left", 8),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
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
    let arena = OldAddress::symbolic(Variable(940_062));
    let native = OldAddress::loaded_value(&memory, &field);
    let mut graph = EqualityGraph::default();
    graph.add_equality(&native, &arena);
    let named_read = |address: &OldAddress| {
        let value = OldAddress::loaded(&load(&memory, address, 8)).unwrap();
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
    let other_stride = OldAddress::loaded(&load(&memory, &field, 8)).unwrap();
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
            graph.add_int32_equality(&offset, &OldMachineTerm::constant(0));
        }
        graph.add_int32_equality(&direct, &var(940_083));
        graph.add_int32_equality(&indexed, &var(940_084));
        if !early {
            assert!(!graph.are_int32_equal(&var(940_083), &var(940_084)));
            graph.add_int32_equality(&offset, &OldMachineTerm::constant(0));
        }
        assert!(
            graph.are_int32_equal(&var(940_083), &var(940_084)),
            "early={early}"
        );
    }
}

#[test]
fn a_late_zero_index_alias_transfers_an_admitted_read_order() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let base = address(940_085);
    let index = var(940_086);
    let direct = load(&memory, &base, 4);
    let indexed = load(&memory, &base.offset_by_elements(index.clone(), 4), 4);
    let next = load(
        &memory,
        &base.offset_by_elements(OldMachineTerm::add(index.clone(), 1u32.into()), 4),
        4,
    );
    let known = OldConditionTerm::signed_less_than(next.clone(), indexed);
    let target = OldConditionTerm::signed_less_than(next, direct);
    let root = PureFactContext::new().assume_condition(known, true);
    assert_eq!(root.decide(&target), None);
    let zero = Proposition::condition_is(OldConditionTerm::equal(index, 0u32.into()), true);
    let equal = root.assume_proposition(zero.clone());
    assert_eq!(equal.decide(&target), Some(true));
    assert_eq!(
        crate::kernel::reasoning::decide_with_facts(&equal, &ExecutionFacts::new(), &target),
        Some(true),
    );
}

/// R-mem: each 32-bit read is its own load, and the two reads of one cell
/// at the two signednesses are related by σ, a node of its own: the
/// `uint32` read is σ of the `int32` read, and reads of two cells stay
/// distinct until their addresses are. Relating them is the same work
/// whatever else the graph holds.
#[test]
fn reads_of_one_cell_at_both_signednesses_are_related() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let read = |pointer: &OldAddress, kind| {
        OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory, pointer, kind, 4,
        ))
    };
    let signed = read(&address(1), crate::kernel::LoadKind::Int32);
    let unsigned = read(&address(1), crate::kernel::LoadKind::UInt32);
    let other = read(&address(2), crate::kernel::LoadKind::UInt32);
    let sigma = |value| {
        OldMachineTerm::sign_cast32(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineIntegerType::UInt32,
            value,
        )
    };
    assert_ne!(signed, unsigned, "each read is its own load");
    let cold_reads = crate::kernel::eval::capture_load_variable_registry();
    let mut samples = Vec::new();
    for unrelated in [4_u64, 64, 512] {
        crate::kernel::eval::restore_load_variable_registry(&cold_reads);
        // Keep term-bridge imports and canonical forms cold at every sample
        // size.
        crate::kernel::clear_machine_observation_memo();
        crate::kernel::eval::clear_load_canonicalization_caches();
        crate::kernel::memory_history::clear_canonical_form_caches();
        let mut graph = EqualityGraph::default();
        for index in 0..unrelated {
            graph.add_int32_equality(&var(500 + index), &var(5_000 + index));
        }
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_int32_equal(&sigma(signed.clone()), &unsigned)
        });
        assert!(equal, "R-mem relates the two reads of one cell by σ");
        assert!(
            !graph.are_int32_equal(&unsigned, &signed),
            "σ is a node of its own"
        );
        assert!(!graph.are_int32_equal(&unsigned, &other));
        graph.add_int32_equality(&var(1), &var(2));
        assert!(graph.are_int32_equal(&sigma(signed.clone()), &other));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

/// R-mem at 16 and 128 bits, as at 8: the signed read of a cell is the
/// sign cast of its unsigned read at the same read key, the cast node a
/// written conversion interns. The two reads stay two terms, and a read of
/// another cell is not related.
#[test]
fn signed_16_and_128_bit_reads_are_the_sign_cast_of_their_unsigned_reads() {
    use crate::kernel::{CarrierWidth as W, LoadKind as K, MachineIntegerType as M};
    for (signed_kind, unsigned_kind, from, to, width, bytes) in [
        (K::Int16, K::UInt16, M::UInt16, M::Int16, W::Bits16, 2),
        (K::Int128, K::UInt128, M::UInt128, M::Int128, W::Bits128, 16),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = memory();
        let read = |pointer: &OldAddress, kind| {
            OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                &memory, pointer, kind, bytes,
            ))
        };
        let signed = read(&address(1), signed_kind);
        let unsigned = read(&address(1), unsigned_kind);
        let other = read(&address(2), unsigned_kind);
        assert_ne!(signed, unsigned, "each read is its own load");
        let cast = |value| OldMachineTerm::machine_integer_cast(from, to, value);
        // A 128-bit equality is decided in its Integer reading
        // (`representation::spells_comparison_natively`); a 16-bit one by its
        // native comparison.
        let equal = |terms: &mut terms::TermClasses,
                     left: OldMachineTerm,
                     right: &OldMachineTerm| {
            if width == W::Bits128 {
                let reading = |value| crate::kernel::IntegerTerm::from_machine(to, value).unwrap();
                terms.are_integer_equal(&reading(left), &reading(right.clone()))
            } else {
                terms.knows_condition(
                    &crate::kernel::OldConditionTerm::Compare {
                        format: to,
                        relation: crate::kernel::CompareRelation::Equal,
                        left: Box::new(left),
                        right: Box::new(right.clone()),
                    },
                    true,
                )
            }
        };
        let graph = EqualityGraph::default();
        let mut state = graph.state.lock().expect("equality graph");
        let terms = &mut state.terms;
        assert!(
            equal(terms, cast(unsigned.clone()), &signed),
            "{to:?}: R-mem relates the two reads of one cell"
        );
        assert!(
            !equal(terms, cast(other.clone()), &signed),
            "{to:?}: a read of another cell is not related"
        );
        // A 16-bit read has a load application, so equal addresses relate
        // the reads of two cells. A 128-bit read is an opaque atom with
        // none: its relation is to its own cell's unsigned read.
        if width == W::Bits16 {
            terms.add_int32_equality(&var(1), &var(2));
            assert!(
                equal(terms, cast(other.clone()), &signed),
                "{to:?}: equal addresses relate their reads"
            );
        }
    }
}

/// A 16-bit constant known of either read of a cell decides the other, as a
/// byte constant does (R-mem), at both ends and both halves of the range.
#[test]
fn a_16_bit_constant_decides_the_other_read_of_its_cell() {
    use crate::kernel::{
        CompareRelation, LoadKind as K, MachineIntegerType as M, OldConditionTerm,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let read = |kind| {
        OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address(1),
            kind,
            2,
        ))
    };
    let (signed, unsigned) = (read(K::Int16), read(K::UInt16));
    let equal = |format, left: &OldMachineTerm, value: i64| OldConditionTerm::Compare {
        format,
        relation: CompareRelation::Equal,
        left: Box::new(left.clone()),
        right: Box::new(OldMachineTerm::narrow_constant(
            format,
            value as u16 as u128,
        )),
    };
    for (signed_value, unsigned_value) in [
        (0, 0),
        (7, 7),
        (32_767, 32_767),
        (-32_768, 32_768),
        (-1, 65_535),
        (-200, 65_336),
    ] {
        let from_signed =
            PureFactContext::new().assume_condition(equal(M::Int16, &signed, signed_value), true);
        assert_eq!(
            from_signed.decide(&equal(M::UInt16, &unsigned, unsigned_value)),
            Some(true),
            "int16 read == {signed_value}"
        );
        assert_eq!(
            from_signed.decide(&equal(M::UInt16, &unsigned, (unsigned_value + 1) % 65_536)),
            Some(false)
        );
        let from_unsigned = PureFactContext::new()
            .assume_condition(equal(M::UInt16, &unsigned, unsigned_value), true);
        assert_eq!(
            from_unsigned.decide(&equal(M::Int16, &signed, signed_value)),
            Some(true),
            "uint16 read == {unsigned_value}"
        );
    }
}

/// Rule K8 as a relation: a sum of the `int32` widenings of `n` narrow
/// loads is interned with constant work per widening, and is σ of the
/// `uint32` sum of the loads' `uint32` widenings (R-dist and R-comp), at
/// every size.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn widening_chains_are_related_with_constant_work_per_widening() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = memory();
    let read = |index: u64| {
        OldMachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address(10_000 + index),
            crate::kernel::LoadKind::UInt8,
            1,
        ))
    };
    let widen = |value: OldMachineTerm| OldMachineTerm::Cast {
        spelling: MachineCastSpelling::Generic,
        value: Box::new(value),
        from: MachineIntegerType::UInt8,
        to: MachineIntegerType::Int32,
    };
    let sizes = [8_u64, 32, 128, 512];
    let cold_reads = crate::kernel::eval::capture_load_variable_registry();
    let mut samples = Vec::new();
    for size in sizes {
        crate::kernel::eval::restore_load_variable_registry(&cold_reads);
        // Keep descriptor caches and term-bridge imports cold at every sample size.
        crate::kernel::clear_machine_observation_memo();
        let word = |value: OldMachineTerm| OldMachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(value),
            from: MachineIntegerType::UInt8,
            to: MachineIntegerType::UInt32,
        };
        let mut widened = widen(read(0));
        let mut words = word(read(0));
        for index in 1..size {
            widened = binary_node!(Int32, Add, Box::new(widened), Box::new(widen(read(index))));
            words = binary_node!(UInt32, Add, Box::new(words), Box::new(word(read(index))));
        }
        let words = OldMachineTerm::sign_cast32(
            MachineIntegerType::UInt32,
            MachineIntegerType::Int32,
            words,
        );
        let mut graph = EqualityGraph::default();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_int32_equality(&widened, &var(900_000 + size));
        });
        assert!(
            graph.are_int32_equal(&var(900_000 + size), &words),
            "size {size}"
        );
        samples.push(work);
    }
    let per_widening =
        |i: usize| (samples[i + 1] - samples[i]) as f64 / (sizes[i + 1] - sizes[i]) as f64;
    for i in 1..sizes.len() - 1 {
        assert_eq!(per_widening(i), per_widening(0), "{samples:?}");
    }
}

#[test]
fn structural_read_graph_registration_keeps_native_version_identity() {
    use crate::kernel::{KernelTermImport, MachineIntegerType, MachineOperandView as V};
    let _session = crate::kernel::VerificationSession::enter();
    let before = memory();
    let pointer = address(993180);
    crate::kernel::eval::record_load_access_width(before.memory(), &pointer, 4);
    let named =
        crate::kernel::canonical_form_of_load(before.clone(), pointer.clone(), LoadKind::Int32);
    let beside = intern_memory(before.memory().clone().store(
        OldAddress {
            base: "beside-array".into(),
            offset: OldAddressOffset::Constant(0).into(),
        },
        ProgramValue::Int32(var(993182)),
    ));
    let raw = OldMachineTerm::read_named(
        ProgramPoint::at(&beside),
        Box::new(pointer.clone()),
        LoadKind::Int32,
    );
    let root = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &raw)
        .unwrap();
    let source = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &named)
        .unwrap();
    let native = EqualityGraph::default().are_int32_equal(&named, &raw);
    assert!(native);
    assert_eq!(
        EqualityGraph::default().are_int32_equal_views(V::Shared(&source), V::Shared(&root)),
        native
    );
    assert_eq!(root.machine_read_leaf(), Some(&raw));
    let changed = OldMachineTerm::read_named(
        ProgramPoint::at(
            &(intern_memory(
                before
                    .memory()
                    .clone()
                    .store(pointer.clone(), ProgramValue::Int32(var(993183))),
            )),
        ),
        Box::new(pointer),
        LoadKind::Int32,
    );
    let changed = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &changed)
        .unwrap();
    assert!(
        !EqualityGraph::default().are_int32_equal_views(V::Shared(&source), V::Shared(&changed))
    );
}

#[test]
fn structural_word_read_requires_its_explicit_store_equation() {
    use crate::kernel::{KernelTermImport, MachineIntegerType, MachineOperandView as V};
    let _session = crate::kernel::VerificationSession::enter();
    let value = OldMachineTerm::PureFunctionApplication {
        name: "opaque_read_value".into(),
        arguments: vec![var(993184)],
    };
    let pointer = address(993185);
    let retained_state = intern_memory(
        memory()
            .memory()
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(value.clone())),
    );
    // The typed word producer supplies its access width before graph queries.
    crate::kernel::eval::record_load_access_width(retained_state.memory(), &pointer, 4);
    let read = OldMachineTerm::read_named(
        ProgramPoint::at(&retained_state),
        Box::new(pointer),
        LoadKind::Int32,
    );
    let shared = KernelTermImport::default()
        .machine_arithmetic(MachineIntegerType::Int32, &read)
        .unwrap();
    let empty = PureFactContext::new();
    assert!(
        !empty
            .equality_graph
            .are_int32_equal_views(V::Shared(&shared), V::Old(&value)),
        "registering a read must not import its cached value"
    );
    assert!(!empty.equality_graph.are_int32_equal(&read, &value));
    let equation = crate::kernel::memory_history::store_value_equation(
        retained_state.memory(),
        &address(993185),
        &ProgramValue::Int32(value.clone()),
    )
    .expect("word store equation");
    let established = empty.clone().assume_proposition(equation);
    assert!(
        established
            .equality_graph
            .are_int32_equal_views(V::Shared(&shared), V::Old(&value))
    );
    assert!(
        !empty
            .equality_graph
            .are_int32_equal_views(V::Shared(&shared), V::Old(&value))
    );
    assert_eq!(shared.machine_read_leaf(), Some(&read));
}
