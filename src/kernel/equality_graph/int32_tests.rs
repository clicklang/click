use super::*;
use crate::kernel::VerificationSession;
use crate::kernel::binary_node;

fn var(id: u64) -> OldMachineTerm {
    OldMachineTerm::Variable(Variable(id))
}

fn eq(left: &OldMachineTerm, right: &OldMachineTerm) -> OldConditionTerm {
    OldConditionTerm::equal(left.clone(), right.clone())
}

fn unsigned_composition(value: OldMachineTerm) -> OldMachineTerm {
    binary_node!(
        Int32,
        BitwiseXor,
        Box::new(binary_node!(
            UInt32,
            Remainder,
            Box::new(value.clone()),
            Box::new(var(90_001)),
        )),
        Box::new(binary_node!(
            UInt32,
            Divide,
            Box::new(value),
            Box::new(var(90_002)),
        )),
    )
}

#[test]
fn unsigned_congruence_propagates_late_aliases_without_injectivity_or_signed_coercion() {
    let (a, b) = (var(90_003), var(90_004));
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let parent = graph.clone();
    graph.add_int32_equality(&a, &b);
    assert!(graph.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let sibling = parent;
    assert!(!sibling.are_int32_equal(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone())
    ));
    let unsigned = binary_node!(
        UInt32,
        Remainder,
        Box::new(a.clone()),
        Box::new(var(90_001))
    );
    let signed = binary_node!(Int32, Remainder, Box::new(b.clone()), Box::new(var(90_001)));
    let quotient = binary_node!(UInt32, Divide, Box::new(b.clone()), Box::new(var(90_001)));
    assert!(!graph.are_int32_equal(&unsigned, &signed));
    assert!(!graph.are_int32_equal(&unsigned, &quotient));
    let mut results_only = EqualityGraph::default();
    results_only.add_int32_equality(
        &unsigned_composition(a.clone()),
        &unsigned_composition(b.clone()),
    );
    assert!(!results_only.are_int32_equal(&a, &b));
    let undefined = binary_node!(
        UInt32,
        Divide,
        Box::new(a),
        Box::new(OldMachineTerm::constant(0))
    );
    assert!(!graph.are_int32_equal(&undefined, &OldMachineTerm::constant(0)));
}

#[test]
fn unsigned_congruence_keeps_load_states_and_widths_distinct() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("unsigned", 4));
    let pointer = OldAddress {
        base: "unsigned".into(),
        offset: OldAddressOffset::Constant(0).into(),
    };
    let after = intern_memory(before.memory().clone().store(
        pointer.clone(),
        ProgramValue::UInt32(OldMachineTerm::constant(9)),
    ));
    let load = |memory, kind| OldMachineTerm::read_named(memory, Box::new(pointer.clone()), kind);
    let old = load(ProgramPoint::at(&before), LoadKind::Int32);
    let value = var(90_012);
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&old, &value);
    assert!(graph.are_int32_equal(
        &unsigned_composition(old),
        &unsigned_composition(value.clone())
    ));
    assert!(!graph.are_int32_equal(
        &unsigned_composition(load(ProgramPoint::at(&after), LoadKind::Int32)),
        &unsigned_composition(value.clone())
    ));
    assert!(!graph.are_int32_equal(
        &unsigned_composition(load(ProgramPoint::at(&before), LoadKind::UInt16)),
        &unsigned_composition(value)
    ));
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
fn shallow_scalar_decision_uses_graph_congruence_and_keeps_branch_scope() {
    let (a, b) = (var(1), var(2));
    let plus_one = |value| {
        binary_node!(
            Int32,
            Add,
            Box::new(value),
            Box::new(OldMachineTerm::constant(1))
        )
    };
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(
        branch.decide_bitvector_equality_shallow(&plus_one(a.clone()), &plus_one(b.clone())),
        Some(true)
    );
    assert_eq!(
        branch.decide(&eq(&plus_one(a.clone()), &plus_one(b.clone()))),
        Some(true)
    );
    assert_ne!(
        parent.decide_bitvector_equality_shallow(&plus_one(a.clone()), &plus_one(b.clone())),
        Some(true)
    );
    assert_ne!(
        parent.decide(&eq(&plus_one(a.clone()), &plus_one(b.clone()))),
        Some(true)
    );
}

#[test]
fn fact_transport_uses_graph_int32_congruence_without_the_legacy_index() {
    let (a, b, limit) = (var(1), var(2), var(3));
    let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    let source = OldConditionTerm::signed_less_than(sum(a.clone()), limit.clone());
    let target = OldConditionTerm::signed_less_than(sum(b.clone()), limit);
    let premise = eq(&a, &b);
    let parent = PureFactContext::new().assume_condition(source.clone(), true);
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.condition_matches(&source, &target));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!parent.condition_matches(&source, &target));
}

#[test]
fn fact_transport_uses_registered_load_congruence_only_in_one_state() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("int32", 16));
    let pointer = |index| OldAddress {
        base: "int32".into(),
        offset: OldAddressOffset::scale_int32(index, 4).into(),
    };
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(11), var(12));
    let after = intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let left = load(&before, a.clone());
    let right = load(&before, b.clone());
    let later = load(&after, b.clone());
    let fact = OldConditionTerm::signed_less_than(left, OldMachineTerm::constant(20));
    let target = OldConditionTerm::signed_less_than(right, OldMachineTerm::constant(20));
    let later_target = OldConditionTerm::signed_less_than(later, OldMachineTerm::constant(20));
    let context = PureFactContext::new().assume_condition(eq(&a, &b), true);
    assert!(context.condition_matches(&fact, &target));
    assert!(!context.condition_matches(&fact, &later_target));
}

#[test]
fn resolved_four_byte_load_uses_graph_value_equality_but_keeps_state_scope() {
    let _session = VerificationSession::enter();
    let pointer = OldAddress {
        base: "resolved-int32".into(),
        offset: OldAddressOffset::Constant(0).into(),
    };
    let (a, b) = (var(31), var(32));
    let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    // A stored byte is a canonical `uint8` carrier: the conversion of the sum.
    let byte = |value| {
        OldMachineTerm::machine_integer_cast(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineIntegerType::UInt8,
            value,
        )
    };
    let before = intern_memory(
        SymbolicMemory::new()
            .with_block("resolved-int32", 4)
            .store(pointer.clone(), ProgramValue::Int32(sum(a.clone()))),
    );
    let after = intern_memory(before.memory().clone().store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let byte_memory = intern_memory(
        SymbolicMemory::new()
            .with_block("resolved-int32", 1)
            .store(pointer.clone(), ProgramValue::UInt8(byte(sum(a.clone())))),
    );
    let load = |memory: &SharedMemory| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let old_load = load(&before);
    let new_load = load(&after);
    let byte_load = OldMachineTerm::Variable(load_variable_for_cell_with_origin(
        &byte_memory,
        &pointer,
        crate::kernel::LoadKind::UInt8,
        1,
        &byte_memory,
    ));
    let target = sum(b.clone());
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(
        branch.resolve_memory_load_term(&old_load),
        Some(sum(a.clone()))
    );
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.memory_loads_proven_equal(&old_load, &target));
    assert!(branch.memory_loads_proven_equal(&target, &old_load));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!branch.memory_loads_proven_equal(&new_load, &target));
    assert_eq!(
        branch.resolve_memory_load_term(&byte_load),
        Some(byte(sum(a)))
    );
    assert!(!branch.memory_loads_proven_equal(&byte_load, &target));
    assert!(!parent.memory_loads_proven_equal(&old_load, &target));
}

#[test]
fn two_resolved_four_byte_loads_compare_values_with_state_scope() {
    let _session = VerificationSession::enter();
    let pointer = |offset| OldAddress {
        base: "two-resolved-int32".into(),
        offset: OldAddressOffset::Constant(offset).into(),
    };
    let (a, b) = (var(41), var(42));
    let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    // A stored byte is a canonical `uint8` carrier: the conversion of the sum.
    let byte = |value| {
        OldMachineTerm::machine_integer_cast(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineIntegerType::UInt8,
            value,
        )
    };
    let left_pointer = pointer(0);
    let right_pointer = pointer(4);
    let before = intern_memory(
        SymbolicMemory::new()
            .with_block("two-resolved-int32", 8)
            .store(left_pointer.clone(), ProgramValue::Int32(sum(a.clone())))
            .store(right_pointer.clone(), ProgramValue::Int32(sum(b.clone()))),
    );
    let after = intern_memory(before.memory().clone().store(
        right_pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let byte_memory = intern_memory(
        SymbolicMemory::new()
            .with_block("two-resolved-int32", 8)
            .store(
                right_pointer.clone(),
                ProgramValue::UInt8(byte(sum(b.clone()))),
            ),
    );
    let load = |memory: &SharedMemory, pointer: &OldAddress, width| {
        let kind = if width == 1 {
            crate::kernel::LoadKind::UInt8
        } else {
            crate::kernel::LoadKind::Int32
        };
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory, pointer, kind, width, memory,
        ))
    };
    let left = load(&before, &left_pointer, 4);
    let right = load(&before, &right_pointer, 4);
    let overwritten = load(&after, &right_pointer, 4);
    let byte_load = load(&byte_memory, &right_pointer, 1);
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert_eq!(branch.resolve_memory_load_term(&left), Some(sum(a)));
    assert_eq!(branch.resolve_memory_load_term(&right), Some(sum(b)));
    assert!(branch.resolve_memory_load_term(&byte_load).is_some());
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(branch.memory_loads_proven_equal(&left, &right));
    assert!(branch.memory_loads_proven_equal(&right, &left));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!branch.memory_loads_proven_equal(&left, &overwritten));
    assert!(!branch.memory_loads_proven_equal(&left, &byte_load));
    assert!(!parent.memory_loads_proven_equal(&left, &right));
}

#[test]
fn direct_composite_int32_argument_uses_graph_with_state_scope() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("resource-value", 8));
    let pointer = |index| OldAddress {
        base: "resource-value".into(),
        offset: OldAddressOffset::scale_int32(index, 4).into(),
    };
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(51), var(52));
    let after = intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let resource = |value| Resource::Composite {
        name: "indexed-value".into(),
        arguments: vec![ProgramValue::Int32(value).into()].into(),
    };
    let left = resource(load(&before, a.clone()));
    let right = resource(load(&before, b.clone()));
    let later = resource(load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(crate::kernel::memory_history::resources_directly_match(
        &left, &right, &branch,
    ));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!crate::kernel::memory_history::resources_directly_match(
        &left, &later, &branch,
    ));
    assert!(!crate::kernel::memory_history::resources_directly_match(
        &left, &right, &parent,
    ));
}

#[test]
fn resource_instance_int32_field_uses_graph_with_state_scope() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("instance-value", 8));
    let pointer = |index| OldAddress {
        base: "instance-value".into(),
        offset: OldAddressOffset::scale_int32(index, 4).into(),
    };
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(61), var(62));
    let after = intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let instance = |value| {
        Resource::Instance(
            ResourceInstance::new(
                InstanceId::from_variable(Variable(6100)),
                "instance-value".into(),
                vec![ProgramValue::Int32(OldMachineTerm::constant(3)).into()].into(),
                schema.clone(),
                vec![ProgramValue::Int32(value).into()].into(),
            )
            .unwrap(),
        )
    };
    let left = instance(load(&before, a.clone()));
    let right = instance(load(&before, b.clone()));
    let later = instance(load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(crate::kernel::memory_history::resources_directly_match(
        &left, &right, &branch,
    ));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!crate::kernel::memory_history::resources_directly_match(
        &left, &later, &branch,
    ));
    assert!(!crate::kernel::memory_history::resources_directly_match(
        &left, &right, &parent,
    ));
}

#[test]
fn certification_uses_graph_int32_equality_with_state_scope() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("certified-int32", 8));
    let pointer = |index| OldAddress {
        base: "certified-int32".into(),
        offset: OldAddressOffset::scale_int32(index, 4).into(),
    };
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(81), var(82));
    let after = intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
    let left = sum(load(&before, a.clone()));
    let right = sum(load(&before, b.clone()));
    let later = sum(load(&after, b.clone()));
    let goal = |right| Proposition::condition_is(eq(&left, &right), true);
    let certifies = |context: &PureFactContext, goal: &Proposition| {
        crate::kernel::PureFactContext::settles_exactly(context, goal)
    };
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(certifies(&branch, &goal(right.clone())));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!certifies(&branch, &goal(later)));
    assert!(!certifies(&parent, &goal(right.clone())));
}

#[test]
fn reordered_sum_matches_graph_equal_load_addends_in_one_state() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("int32", 16));
    let pointer = |index| OldAddress {
        base: "int32".into(),
        offset: OldAddressOffset::scale_int32(index, 4).into(),
    };
    let load = |memory: &SharedMemory, index| {
        OldMachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (var(21), var(22));
    let after = intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let sum = |value, other| OldMachineTerm::add(value, other);
    let fixed = var(23);
    let left = sum(load(&before, a.clone()), fixed.clone());
    let right = sum(fixed.clone(), load(&before, b.clone()));
    let later = sum(fixed, load(&after, b.clone()));
    let premise = eq(&a, &b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    assert!(!branch.equality_graph.are_int32_equal(&left, &right));
    assert!(branch.bitvector_add_terms_proven_equal(&left, &right));
    assert_eq!(branch.decide(&eq(&left, &right)), Some(true));
    assert!(!branch.bitvector_add_terms_proven_equal(&left, &later));
    assert!(!parent.bitvector_add_terms_proven_equal(&left, &right));
}

#[test]
fn int32_classes_are_typed_and_integer_operators_have_congruence() {
    let (a, b) = (var(1), var(2));
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&a, &b);
    assert!(!graph.are_offsets_equal(
        &crate::kernel::AddressOffset::from(&OldAddressOffset::Variable(Variable(1))),
        &crate::kernel::AddressOffset::from(&OldAddressOffset::Variable(Variable(2))),
    ));
    assert!(!graph.are_equal(
        &OldAddress::symbolic(Variable(1)),
        &OldAddress::symbolic(Variable(2))
    ));
    assert!(graph.are_offsets_equal(
        &crate::kernel::AddressOffset::from(&OldAddressOffset::scale_int32(a.clone(), 4)),
        &crate::kernel::AddressOffset::from(&OldAddressOffset::scale_int32(b.clone(), 4)),
    ));
    let plus_one = |value| {
        binary_node!(
            Int32,
            Add,
            Box::new(value),
            Box::new(OldMachineTerm::constant(1))
        )
    };
    assert!(graph.are_int32_equal(&plus_one(a.clone()), &plus_one(b.clone())));
    let minus_one = |value| {
        binary_node!(
            Int32,
            Subtract,
            Box::new(value),
            Box::new(OldMachineTerm::constant(1))
        )
    };
    assert!(graph.are_int32_equal(&minus_one(a.clone()), &minus_one(b.clone())));
    assert!(!graph.are_int32_equal(&plus_one(a), &minus_one(b)));
    graph.add_offset_equality(
        &crate::kernel::AddressOffset::from(&OldAddressOffset::Variable(Variable(3))),
        &crate::kernel::AddressOffset::from(&OldAddressOffset::Variable(Variable(4))),
    );
    assert!(!graph.are_int32_equal(&var(3), &var(4)));
    assert!(!graph.are_int32_equal(&OldMachineTerm::constant(0), &OldMachineTerm::constant(1)));
}

#[test]
fn int32_restriction_and_contradiction_preserve_support() {
    let (a, b, c) = (var(10), var(11), var(12));
    let ab = eq(&a, &b);
    let bc = eq(&b, &c);
    let offset = |i| OldAddressOffset::Variable(Variable(i));
    let pq = OldConditionTerm::address_equal(
        OldAddress::symbolic(Variable(20)),
        OldAddress::symbolic(Variable(21)),
    );
    let xy = OldConditionTerm::address_offset_equal(offset(30).into(), offset(31).into());
    let context = PureFactContext::new()
        .assume_condition(ab.clone(), true)
        .assume_condition(bc.clone(), true)
        .assume_condition(pq.clone(), true)
        .assume_condition(xy.clone(), true);
    assert!(context.equality_graph.are_int32_equal(&a, &c));
    let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let replaced = context.clone().assume_condition(bc, false);
    assert!(replaced.is_inconsistent());
    assert!(replaced.equality_graph.are_int32_equal(&a, &c));
    assert!(context.equality_graph.are_int32_equal(&a, &c));
}

#[test]
fn int32_load_identity_keeps_states_separate() {
    let _session = VerificationSession::enter();
    let before = intern_memory(SymbolicMemory::new().with_block("int32", 8));
    let pointer = OldAddress::symbolic(Variable(40));
    let after = intern_memory(before.memory().clone().store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let load = |memory: &SharedMemory| {
        OldMachineTerm::read_named(
            ProgramPoint::at(memory),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        )
    };
    let named = OldMachineTerm::Variable(load_variable_for_cell_with_origin(
        &before,
        &pointer,
        crate::kernel::LoadKind::Int32,
        4,
        &before,
    ));
    let a = var(41);
    let context = PureFactContext::new()
        .assume_condition(eq(&load(&before), &a), true)
        .assume_condition(eq(&named, &a), true);
    assert!(context.equality_graph.are_int32_equal(&load(&before), &a));
    assert!(!context.equality_graph.are_int32_equal(&load(&after), &a));
    let scale = |value| OldAddressOffset::scale_int32(value, 4);
    assert!(context.equality_graph.are_offsets_equal(
        &crate::kernel::AddressOffset::from(&scale(load(&before))),
        &crate::kernel::AddressOffset::from(&scale(a.clone()))
    ));
    assert!(!context.equality_graph.are_offsets_equal(
        &crate::kernel::AddressOffset::from(&scale(load(&after))),
        &crate::kernel::AddressOffset::from(&scale(a.clone()))
    ));
    let sum = |value| binary_node!(Int32, Add, Box::new(value), Box::new(var(42)));
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
}

#[test]
fn offset_premises_support_scalar_graph_edges() {
    let (a, b, c) = (var(70), var(71), var(72));
    let offset_eq = |left: OldMachineTerm, right: OldMachineTerm| {
        OldConditionTerm::address_offset_equal(
            OldAddressOffset::scale_int32(left, 4).into(),
            OldAddressOffset::scale_int32(right, 4).into(),
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
    let restricted = context.restricted_to_facts(&[(scaled, true)], &[]);
    assert!(restricted.equality_graph.are_int32_equal(&a, &b));
    assert!(!restricted.equality_graph.are_int32_equal(&a, &c));
    let mut context = PureFactContext::new();
    for width in [0, 1, 8] {
        context = context.assume_condition(
            OldConditionTerm::address_offset_equal(
                OldAddressOffset::scaled_int32_node(a.clone(), width).into(),
                OldAddressOffset::scaled_int32_node(b.clone(), width).into(),
            ),
            true,
        );
    }
    assert!(
        !context.equality_graph.are_int32_equal(&a, &b),
        "this ingress only translates four-byte element-index premises"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/int32_tests.rs");
}

#[test]
fn parameter_shortcuts_notice_byte_coordinates_inside_an_alias_expression() {
    let _session = VerificationSession::enter();
    let offset = |i: u64| OldAddressOffset::Variable(Variable(995_000 + i));
    let input = OldConditionTerm::AddressOffsetEqual(
        Box::new(OldAddressOffset::Add(Box::new(offset(0)), Box::new(offset(1))).into()),
        Box::new(offset(2).into()),
    );
    let facts = PureFactContext::new().assume_condition(input.clone(), true);
    assert!(
        facts
            .equality_graph
            .offset_has_source_dependencies(&crate::kernel::AddressOffset::from(&offset(1)))
    );
    assert!(
        !facts
            .equality_graph
            .offset_has_source_dependencies(&crate::kernel::AddressOffset::from(&offset(3)))
    );
}

#[test]
fn complete_pointer_equalities_supply_only_their_true_numeric_consequences() {
    let _session = VerificationSession::enter();
    let pointer = |id| {
        OldPointer::new(
            OldAddress {
                base: AddressBase::ExternalArgument,
                offset: OldAddressOffset::scale_int32(var(id), 4).into(),
            },
            ProgramType::Int32Pointer,
        )
    };
    let (left, right) = (pointer(941_001), pointer(941_002));
    let equality = OldConditionTerm::pointer_equal(left.clone(), right.clone());
    assert!(equality.pointer_offset_sides().is_none());
    let context = PureFactContext::new().assume_condition(equality.clone(), true);
    assert!(
        context
            .recorded_equality_class(&var(941_001))
            .contains(&var(941_002))
    );
    assert!(
        context
            .equality_graph
            .offset_has_source_dependencies(&left.offset)
    );
    let negative = PureFactContext::new().assume_condition(equality, false);
    assert!(
        !negative
            .recorded_equality_class(&var(941_001))
            .contains(&var(941_002))
    );
    let numeric = PureFactContext::new().assume_condition(eq(&var(941_001), &var(941_002)), true);
    assert!(!numeric.pointer_provenance_match(&left, &right));
}

#[test]
fn recorded_shared_index_members_keep_source_order_without_exporting() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, MachineBinaryOp as O, MachineIntegerType as T,
        MachineOperandView as V, SharedMachineIntegerTerm as S,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let x = var(1081701);
    let y = var(1081702);
    let shared = |term: &OldMachineTerm| {
        let root = KernelTerm::retained_machine_operand(T::Int32, V::Old(term));
        S::from_shared(
            T::Int32,
            KernelTerm::machine_binary_shared(T::Int32, O::Add, [root.clone(), root]),
        )
        .unwrap()
    };
    let left = shared(&x);
    let right = shared(&y);
    let equality = OldConditionTerm::AddressOffsetEqual(
        Box::new(crate::kernel::AddressOffset::from(
            OldAddressOffset::Int32Scaled {
                value: left.clone(),
                byte_width: 4,
            },
        )),
        Box::new(crate::kernel::AddressOffset::from(
            OldAddressOffset::Int32Scaled {
                value: right.clone(),
                byte_width: 4,
            },
        )),
    );
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(equality.clone(), true);
    let exports = KernelTermExport::machine_export_count();
    let members = facts.recorded_equality_class_view(left.operand_view());
    assert!(members.iter().any(|member| {
        crate::kernel::machine_operand_syntax_cmp(member.operand_view(), right.operand_view())
            .is_eq()
    }));
    assert!(
        empty
            .recorded_equality_class_view(left.operand_view())
            .is_empty()
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}
