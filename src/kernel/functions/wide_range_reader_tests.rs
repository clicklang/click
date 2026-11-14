use super::*;
// Both symbolic bases and native extents reach call-framing readers.
#[test]
fn wide_call_ranges_are_undecided() {
    let base = Pointer::symbolic(Variable(984_000));
    let wide = MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(3),
        MachineTerm::uint64_constant(1 << 33),
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
}
// Wide resource bodies are opened, folded and queried without constructing
// signed loadability facts in the instance and ordinary-composite paths.
#[test]
fn wide_resource_body_loadability_preserves_native_extent() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(984_010));
    let segment = MemorySegment::new(
        ProgramExpression::Value(ProgramValue::pointer(base.clone())),
        c_uint64_literal(0),
        c_uint64_literal(1 << 33),
    )
    .with_element_width(1);
    let schema = ResourceFieldSchema::new(vec![(
        "length".into(),
        ResourceFieldType::C(ProgramType::UInt64),
    )])
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "wide",
        vec![],
        None,
        false,
        vec![ResourceSpec::owned_memory(segment)],
        vec![],
    )
    .with_instance_schema(Some(schema.clone()));
    let instance = ResourceInstance::new(
        Variable(984_011),
        "wide".into(),
        vec![].into(),
        schema,
        vec![AlgebraicValue::C(ProgramValue::UInt64(
            MachineTerm::uint64_constant(1 << 33),
        ))]
        .into(),
    )
    .unwrap();
    let held = ResourceFact::own(Resource::Instance(instance.clone()));
    let state = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(held.clone()));
    let facts = PureFactContext::new();
    let definitions = [definition.clone()];
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
    let composite = ResourceFact::own(Resource::Composite {
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
