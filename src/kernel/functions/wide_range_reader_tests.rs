use super::*;
// Both symbolic bases and native extents reach call-framing readers.
#[test]
fn wide_call_ranges_are_undecided_and_canonical_pointers_keep_their_width() {
    let base = Pointer::symbolic(Variable(984_000));
    let wide = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(3),
        Bitvector32Term::UInt64Constant(1 << 33),
        1,
    );
    let other = wide.with_base(base.offset_by_bytes(1));
    let facts = PureFactContext::new();
    assert_eq!(
        candidate_memory_ranges_relation_by_bounds(&wide, &other, &facts),
        CandidateMemoryRangeRelation::SeparationUnproved
    );
    assert!(!candidate_memory_ranges_proven_separate(
        &wide, &other, &facts
    ));
    let checked_base = Pointer::symbolic(Variable(984_001));
    let checked =
        CMemoryRange::new_with_element_width(checked_base.clone(), 0u32.into(), 1u32.into(), 1);
    let slot = Pointer {
        block: "wide_canonical_pointer_slot".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new().with_memory(
        CMemory::new()
            .with_block(slot.block.clone(), 8)
            .store(slot.clone(), CValue::pointer(checked_base)),
    );
    let canonical = with_canonical_borrowed_pointer_memory(
        &state,
        &[(
            CResourceFact::own_memory(checked),
            CResourceFact::own_memory(wide.clone()),
        )],
    );
    assert_eq!(
        canonical.memory().known_value(&slot),
        Some(CValue::pointer(wide.start_pointer()))
    );
}
// Wide resource bodies are opened, folded and queried without constructing
// signed loadability facts in the instance and ordinary-composite paths.
#[test]
fn wide_resource_body_loadability_preserves_native_extent() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(984_010));
    let segment = CMemorySegment::new(
        CExpression::Value(CValue::pointer(base.clone())),
        c_uint64_literal(0),
        c_uint64_literal(1 << 33),
    )
    .with_element_width(1);
    let schema =
        ResourceFieldSchema::new(vec![("length".into(), ResourceFieldType::C(CType::UInt64))])
            .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "wide",
        vec![],
        None,
        false,
        vec![CResourceSpec::owned_memory(segment)],
        vec![],
    )
    .with_instance_schema(Some(schema.clone()));
    let instance = ResourceInstance::new(
        Variable(984_011),
        "wide".into(),
        vec![].into(),
        schema,
        vec![AlgebraicValue::C(CValue::UInt64(
            Bitvector32Term::UInt64Constant(1 << 33),
        ))]
        .into(),
    )
    .unwrap();
    let held = CResourceFact::own(CResource::Instance(instance.clone()));
    let state = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held.clone()));
    let facts = PureFactContext::new();
    let definitions = [definition.clone()];
    let (ranges, _) =
        unmatched_instance_body_ownership(&held, &definitions, &state, &facts).unwrap();
    assert_eq!(ranges.len(), 1);
    assert!(ranges[0].wide_bounds().is_some());
    let opened = rewrite_resource_instance_selecting_children_unspelled(
        &state,
        &instance,
        &definition,
        &definitions,
        &facts,
        true,
        None,
    )
    .unwrap();
    assert!(opened.state.resources().facts().iter().any(|fact| {
        fact.memory_range()
            .is_some_and(|range| range.wide_bounds().is_some())
    }));
    let composite = CResourceFact::own(CResource::Composite {
        name: "wide".into(),
        arguments: vec![].into(),
    });
    let loadable = evaluate_composite_resource_loadable_propositions(
        &composite,
        &definitions,
        state.memory(),
        &facts,
    )
    .unwrap();
    assert!(
        loadable
            .iter()
            .any(|fact| matches!(fact, Proposition::CMemoryLoadable { wide: true, .. }))
    );
}
