use super::*;

fn at(id: u64) -> Pointer {
    Pointer::symbolic(Variable(8_750_000 + id))
}
fn owner(base: Pointer, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        start.into(),
        end.into(),
        1,
    ))
}

#[test]
fn indexed_ownership_overlap_keeps_geometry_and_persistent_branches() {
    let empty = PureFactContext::new();
    let q = at(0);
    let p = at(1);
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(p.clone(), q.offset_by_bytes(2)),
        true,
    );
    let held = owner(q.clone(), 4, 8);
    {
        let _operation = crate::kernel::search::FastOperationScope::enter("constant output batch");
        assert!(
            ResourceContext::new_with_equalities(&facts)
                .try_compose_into_valid_context_delaying_normalization(
                    [owner(q.clone(), 0, 4), owner(p.clone(), 2, 6)],
                    &facts
                )
                .is_ok()
        );
    }
    let parent = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held.clone());
    parent.synchronize_memory_equalities(&empty);
    for (start, end, overlap) in [(0, 2, false), (0, 4, true), (6, 8, false)] {
        let added = owner(p.clone(), start, end);
        let _operation =
            crate::kernel::search::FastOperationScope::enter("indexed translated ownership");
        let result = parent
            .clone()
            .try_compose_into_valid_context_delaying_normalization([added], &facts);
        assert_eq!(result.is_err(), overlap);
    }
    // The sibling without the equality must not inherit its class merge.
    assert!(
        parent
            .clone()
            .try_compose_into_valid_context_delaying_normalization([owner(p.clone(), 0, 4)], &empty)
            .is_ok()
    );
    assert!(parent.contains_exact_representation(&held));
    assert_eq!(parent.facts().len(), 1);
    let removed = parent.clone().without_exact_representation(&held).unwrap();
    assert!(
        removed
            .try_compose_into_valid_context_delaying_normalization([owner(q, 4, 8)], &facts)
            .is_ok()
    );
    // Different element widths still describe the same physical bytes.
    let added = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p,
        0u32.into(),
        1u32.into(),
        4,
    ));
    assert!(
        parent
            .clone()
            .try_compose_into_valid_context_delaying_normalization([added], &facts)
            .is_err()
    );
    let native = ResourceFact::own_memory(MemoryRange::new_wide(
        at(1),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(4),
        1,
    ));
    assert!(
        parent
            .try_compose_into_valid_context_delaying_normalization([native], &facts)
            .is_err()
    );
}

#[test]
fn a_query_read_definition_is_registered_in_the_paired_namespace() {
    let facts = PureFactContext::new();
    let pointer = at(10);
    let resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(
        pointer.clone(),
        0,
        4,
    ));
    resources.synchronize_memory_equalities(&facts);
    let field = at(11);
    let memory = Memory::new().store(
        field.clone(),
        ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
    );
    let retained_state = crate::kernel::intern_memory_ref(&memory);
    let variable = crate::kernel::load_variable_for_cell_with_origin(
        &retained_state,
        &field,
        LoadKind::Int32,
        C_POINTER_BYTE_WIDTH,
        &retained_state,
    );
    let read = Pointer::loaded(&MachineTerm::Variable(variable)).unwrap();
    facts.register_pointer_read(&read, &retained_state, &field);
    let _operation = crate::kernel::search::FastOperationScope::enter(
        "ownership through a newly registered read",
    );
    assert!(
        resources
            .try_compose_into_valid_context_delaying_normalization([owner(read, 0, 4)], &facts)
            .is_err()
    );
}

#[test]
fn incomplete_indexes_refuse_but_cold_maintained_coordinates_decide() {
    let facts = PureFactContext::new();
    let p = at(2);
    let symbolic = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p.clone(),
        0u32.into(),
        MachineTerm::Variable(Variable(8_760_000)),
        1,
    ));
    let resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(symbolic);
    resources.synchronize_memory_equalities(&facts);
    let _operation =
        crate::kernel::search::FastOperationScope::enter("unsupported ownership shape");
    assert!(matches!(
        resources.constant_owned_overlap(&owner(p.clone(), 0, 4), &facts),
        ConstantOwnedOverlap::Unsupported
    ));
    let raw = ResourceContext::new().unchecked_with_fact(owner(p.clone(), 4, 8));
    assert!(matches!(
        raw.constant_owned_overlap(&owner(p, 0, 4), &facts),
        ConstantOwnedOverlap::Clear
    ));
}

#[test]
fn pooled_literal_ownership_keeps_the_existing_memory_algebra_policy() {
    let literal = |identity| Pointer {
        block: PointerBlock::StringLiteral {
            identity: StringLiteralId::new(identity, 0),
            bytes: b"ok\0".to_vec(),
        },
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = literal("overlap:left");
    let right = literal("overlap:right");
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(left.clone(), right.clone()),
        true,
    );
    let resources =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owner(left, 0, 2));
    resources.synchronize_memory_equalities(&facts);
    assert!(matches!(
        resources.constant_owned_overlap(&owner(right.clone(), 0, 2), &facts),
        ConstantOwnedOverlap::Unsupported
    ));
    assert!(
        resources
            .try_compose_into_valid_context_delaying_normalization([owner(right, 0, 2)], &facts)
            .is_ok()
    );
}

#[test]
fn cold_ownership_uses_produced_intervals_without_preparing_a_graph() {
    let facts = PureFactContext::new();
    let p = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(8_760_010)),
    };
    let long = owner(p.clone(), 0, 100);
    // A nested old interval must not hide the long interval from a query.
    let parent = ResourceContext::new().unchecked_with_facts([long, owner(p.clone(), 2, 3)]);
    let _fast =
        crate::kernel::search::FastOperationScope::enter("cold produced ownership intervals");
    assert!(matches!(
        parent.constant_owned_overlap(&owner(p.clone(), 5, 6), &facts),
        ConstantOwnedOverlap::Overlap(_)
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&owner(p.clone(), 100, 104), &facts),
        ConstantOwnedOverlap::Clear
    ));
    assert!(parent.memory_equalities.lock().unwrap().published.is_none());
    let removed = parent
        .clone()
        .without_exact_representation(&owner(p.clone(), 0, 100))
        .unwrap();
    assert!(matches!(
        removed.constant_owned_overlap(&owner(p.clone(), 5, 6), &facts),
        ConstantOwnedOverlap::Clear
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&owner(p, 5, 6), &facts),
        ConstantOwnedOverlap::Overlap(_)
    ));
}

#[test]
fn symbolic_boundary_uses_direct_bounds_and_does_not_invent_an_overlap() {
    let p = at(30);
    let x = MachineTerm::Variable(Variable(8_760_030));
    let empty = PureFactContext::new();
    let parent = ResourceContext::new().unchecked_with_fact(owner(p.clone(), 8, 12));
    let query = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        p.clone(),
        0u32.into(),
        x.clone(),
        1,
    ));
    let bounded = |lo: u32, hi: u32| {
        empty
            .clone()
            .assume_condition(ConditionTerm::signed_less_equal(lo.into(), x.clone()), true)
            .assume_condition(ConditionTerm::signed_less_equal(x.clone(), hi.into()), true)
    };
    let _fast =
        crate::kernel::search::FastOperationScope::enter("explicit symbolic return boundary");
    assert!(matches!(
        parent.constant_owned_overlap(&query, &empty),
        ConstantOwnedOverlap::Unsupported
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&query, &bounded(2, 4)),
        ConstantOwnedOverlap::Clear
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&query, &bounded(2, 10)),
        ConstantOwnedOverlap::Unsupported
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&query, &bounded(9, 9)),
        ConstantOwnedOverlap::Overlap(_)
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&query, &bounded(0, 0)),
        ConstantOwnedOverlap::Clear
    ));
    assert!(matches!(
        parent.constant_owned_overlap(&query, &empty),
        ConstantOwnedOverlap::Unsupported
    ));
}
