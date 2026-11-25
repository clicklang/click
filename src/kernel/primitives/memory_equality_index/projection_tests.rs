use super::*;
use crate::kernel::*;

// Observe only this test's composite expansion/coverage input; release builds omit the hook
// and no retained contexts or extra clones in other tests.
thread_local! {
    static OBSERVED_CONTEXT: std::cell::RefCell<Option<Option<ResourceContext>>> = const { std::cell::RefCell::new(None) };
}

pub(super) fn record_context(context: &ResourceContext) {
    OBSERVED_CONTEXT.with(|cell| {
        if let Some(capture) = cell.borrow_mut().as_mut() {
            *capture = Some(context.clone());
        }
    });
}

fn projection_context(
    head: &ResourceFact,
    definition: &CompositeResourceDefinition,
    memory: &SymbolicMemory,
    facts: &PureFactContext,
) -> ResourceContext {
    capture_context(|| {
        assert!(
            crate::kernel::functions::checked_composite_projection_evidence(
                head,
                std::slice::from_ref(definition),
                &ProgramPoint::of_memory(memory),
                facts,
            )
            .is_some(),
            "the viewed body must expand"
        );
    })
}

fn capture_context(operation: impl FnOnce()) -> ResourceContext {
    struct Restore(Option<Option<ResourceContext>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OBSERVED_CONTEXT.with(|cell| *cell.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(OBSERVED_CONTEXT.with(|cell| cell.replace(Some(None))));
    operation();
    OBSERVED_CONTEXT.with(|cell| cell.borrow_mut().as_mut().unwrap().take().unwrap())
}

fn owned_frontier_context(
    head: &ResourceFact,
    definition: &CompositeResourceDefinition,
    state: &ExecutionState,
    facts: &PureFactContext,
) -> ResourceContext {
    capture_context(|| {
        let frontier = crate::kernel::functions::checked_one_level_frontier(
            head,
            std::slice::from_ref(definition),
            state,
            facts,
        )
        .expect("the owned body must expand");
        assert_eq!(frontier.len(), 2);
        assert!(frontier.iter().all(ResourceFact::is_own));
    })
}

fn prior_child(context: ResourceContext, head: &ResourceFact) -> ResourceContext {
    let child = ResourceFact::own_memory(MemoryRange::new(
        Address::symbolic(Variable(881_000)),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
    ));
    context
        .without_exact_representation(head)
        .unwrap()
        .unchecked_with_fact(child)
}

fn fixture() -> (
    ResourceFact,
    CompositeResourceDefinition,
    SymbolicMemory,
    PureFactContext,
    PureFactContext,
) {
    let at = |id| Address::symbolic(Variable(id));
    let (slot, middle, alias, target) = (at(881_000), at(881_001), at(881_002), at(881_003));
    let typed = |pointer| ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer);
    let head = ResourceFact::view_composite(
        "dependent_projection".into(),
        vec![
            typed(slot.clone()),
            typed(alias.clone()),
            typed(target.clone()),
        ],
    );
    let definition = CompositeResourceDefinition::new(
        "dependent_projection",
        vec![
            program_parameter("slot", ProgramType::Int32Pointer),
            program_parameter("alias", ProgramType::Int32Pointer),
            program_parameter("target", ProgramType::Int32Pointer),
        ],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("slot"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            )),
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("target"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::load(
                    crate::kernel::program_expression::variable("alias"),
                ),
            )),
        ],
        Vec::new(),
    );
    let memory = SymbolicMemory::new()
        .with_block(slot.base.clone(), 4)
        .with_block(target.base, 8)
        .store(slot.clone(), int32(2u32));
    let sibling = PureFactContext::new()
        .assume_condition(
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(882_000)),
                OldMachineTerm::Variable(Variable(882_001)),
            ),
            true,
        )
        .assume_condition(OldConditionTerm::address_equal(slot, middle.clone()), true);
    let branch = sibling
        .clone()
        .assume_condition(OldConditionTerm::address_equal(middle, alias), true);
    (head, definition, memory, branch, sibling)
}

#[test]
fn dependent_composite_projection_selects_the_prior_child_by_graph_address() {
    let (head, definition, memory, branch, sibling) = fixture();
    // Logical loads may bypass permission checks, so successful expansion
    // alone cannot establish that its resource index follows the graph.
    let context = projection_context(&head, &definition, &memory, &branch);
    let children = prior_child(context, &head);
    let alias = Address::symbolic(Variable(881_002));
    let entries = children.concrete_read_entries(&alias, 4, &branch);
    assert!(
        entries.is_some_and(|entries| entries.exact()),
        "projection context did not attach the prior child's graph address payload"
    );
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(!children.permits_memory_read(&alias, 4, &sibling));
    assert!(!children.permits_memory_read(&alias.offset_by_bytes(4), 4, &branch));
    assert!(!children.permits_memory_read(&alias, 12, &branch));
    let sibling_children = prior_child(
        projection_context(&head, &definition, &memory, &sibling),
        &head,
    );
    assert!(!sibling_children.permits_memory_read(&alias, 4, &sibling));
    // Querying another fork cannot contaminate either branch's payload.
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(sibling_children.facts().iter().all(ResourceFact::is_own));
}

#[test]
fn projection_evidence_still_requires_a_viewed_head_and_matching_definition() {
    let (head, definition, memory, facts, _) = fixture();
    let owned = ResourceFact::own(head.resource().clone());
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &owned,
            std::slice::from_ref(&definition),
            &ProgramPoint::of_memory(&memory),
            &facts,
        )
        .is_none()
    );
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &head,
            &[],
            &ProgramPoint::of_memory(&memory),
            &facts,
        )
        .is_none()
    );
}

#[test]
fn owned_composite_frontier_selects_the_prior_child_by_graph_address() {
    let (viewed, definition, memory, branch, sibling) = fixture();
    let head = ResourceFact::own(viewed.resource().clone());
    let state = ExecutionState::new().with_memory(memory);
    let context = owned_frontier_context(&head, &definition, &state, &branch);
    let children = prior_child(context, &head);
    let alias = Address::symbolic(Variable(881_002));
    assert!(
        children
            .concrete_read_entries(&alias, 4, &branch)
            .is_some_and(|entries| entries.exact()),
        "owned frontier context did not attach the prior child's graph address payload"
    );
    assert!(children.permits_memory_read(&alias, 4, &branch));
    assert!(!children.permits_memory_read(&alias, 4, &sibling));
    assert!(!children.permits_memory_read(&alias.offset_by_bytes(4), 4, &branch));
    assert!(!children.permits_memory_read(&alias, 12, &branch));
    let sibling_children = prior_child(
        owned_frontier_context(&head, &definition, &state, &sibling),
        &head,
    );
    assert!(!sibling_children.permits_memory_read(&alias, 4, &sibling));
    assert!(children.permits_memory_read(&alias, 4, &branch));
}

fn coverage_context(
    available: Vec<ResourceFact>,
    required: &[ResourceFact],
    facts: &PureFactContext,
) -> (ResourceContext, Option<ResourceContext>) {
    let mut residual = None;
    let input = capture_context(|| {
        residual = crate::kernel::functions::checked_frontier_coverage(available, required, facts);
    });
    (input, residual)
}

fn coverage_piece(id: u64, start: u32, end: u32) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(
        Address::symbolic(Variable(id)),
        OldMachineTerm::constant(start),
        OldMachineTerm::constant(end),
    ))
}

#[test]
fn frontier_coverage_selects_and_consumes_through_transitive_address_equality() {
    let (_, _, _, branch, sibling) = fixture();
    let owner = coverage_piece(881_000, 0, 1);
    let wanted = coverage_piece(881_002, 0, 1);
    let (input, residual) =
        coverage_context(vec![owner.clone()], std::slice::from_ref(&wanted), &branch);
    assert!(
        input
            .concrete_write_entries(&Address::symbolic(Variable(881_002)), 4, &branch)
            .is_some_and(|entries| entries.exact()),
        "frontier coverage bypassed the graph's whole-cell ownership payload"
    );
    assert!(
        residual
            .expect("equal addresses cover the requested piece")
            .is_empty()
    );
    assert!(
        coverage_context(vec![owner.clone()], std::slice::from_ref(&wanted), &sibling)
            .1
            .is_none()
    );
    assert!(
        coverage_context(
            vec![owner.clone()],
            &[coverage_piece(881_002, 0, 2)],
            &branch
        )
        .1
        .is_none()
    );
    assert!(
        coverage_context(vec![owner.clone()], &[wanted.clone(), wanted], &branch)
            .1
            .is_none(),
        "one occurrence cannot back the requested piece twice"
    );
    assert!(
        coverage_context(
            vec![ResourceFact::View(owner.resource().clone())],
            &[coverage_piece(881_002, 0, 1)],
            &branch
        )
        .1
        .is_none(),
        "a view must not supply owned coverage"
    );
    assert!(
        coverage_context(vec![owner], &[coverage_piece(881_002, 1, 2)], &branch)
            .1
            .is_none()
    );
}

#[test]
fn frontier_coverage_splits_ownership_and_preserves_the_input_state() {
    let (_, _, _, facts, _) = fixture();
    let wanted = coverage_piece(881_002, 0, 1);
    let (input, residual) = coverage_context(
        vec![coverage_piece(881_000, 0, 3)],
        std::slice::from_ref(&wanted),
        &facts,
    );
    let residual = residual.expect("partial coverage splits the owner");
    assert_eq!(residual.facts(), &[coverage_piece(881_000, 1, 3)]);
    assert!(
        residual
            .clone()
            .without_fact_incrementally(&coverage_piece(881_002, 1, 3), &facts)
            .expect("the same graph-aware coverage path consumes the residual")
            .is_empty()
    );
    assert!(
        residual
            .without_fact_incrementally(&wanted, &facts)
            .is_none()
    );
    assert_eq!(
        input.facts(),
        &[coverage_piece(881_000, 0, 3)],
        "proof-local consumption must preserve the input state"
    );
}

#[test]
fn resource_satisfaction_uses_transitive_addresses_without_restoring_consumed_ownership() {
    let (_, _, _, facts, sibling) = fixture();
    let original = ResourceContext::new()
        .try_compose_with_fact(coverage_piece(881_000, 0, 3), &facts)
        .unwrap();
    let residual = original
        .clone()
        .without_fact_incrementally(&coverage_piece(881_002, 0, 1), &facts)
        .unwrap();
    let wanted = coverage_piece(881_002, 1, 3);
    assert!(residual.satisfies_fact(&wanted, &facts));
    assert!(!residual.satisfies_fact(&wanted, &sibling));
    assert!(!residual.satisfies_fact(&coverage_piece(881_002, 0, 1), &facts));
    assert!(!residual.satisfies_fact(&coverage_piece(881_002, 1, 4), &facts));
    let alias = Address::symbolic(Variable(881_002));
    let shifted = ResourceFact::own_memory(MemoryRange::new(
        alias.offset_by_elements(OldMachineTerm::constant(1), 4),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(2),
    ));
    assert!(residual.satisfies_fact(&shifted, &facts));
    let bytes = |end| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            alias.clone(),
            OldMachineTerm::constant(4),
            OldMachineTerm::constant(end),
            1,
        ))
    };
    assert!(residual.satisfies_fact(&bytes(12), &facts));
    assert!(!residual.satisfies_fact(&bytes(13), &facts));
    assert!(residual.satisfies_fact(&ResourceFact::View(wanted.resource().clone()), &facts));
    assert!(original.satisfies_fact(&coverage_piece(881_002, 0, 3), &facts));
    assert_eq!(residual.facts(), &[coverage_piece(881_000, 1, 3)]);
    let viewed = ResourceContext::new()
        .try_compose_with_fact(
            ResourceFact::View(coverage_piece(881_000, 1, 3).resource().clone()),
            &facts,
        )
        .unwrap();
    assert!(!viewed.satisfies_fact(&wanted, &facts));
}

#[test]
fn framing_producer_leaves_non_direct_ownership_opaque() {
    let (head, definition, _, facts, sibling) = fixture();
    let head = ResourceFact::own(head.resource().clone());
    let residual = ResourceContext::new()
        .try_compose_with_fact(head, &facts)
        .unwrap();
    let kept =
        crate::kernel::functions::call_kept_ownership(&residual, &[definition].into(), &facts);
    let opened = kept.opened_resources_for_test();
    assert!(
        opened.is_empty(),
        "call framing must not open the retained body"
    );
    assert!(!opened.satisfies_fact(&coverage_piece(881_002, 0, 1), &facts));
    assert!(!opened.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
    assert_eq!(residual.facts().len(), 1);
}

#[test]
fn fresh_resource_publication_tracks_late_equalities_and_persistent_deltas() {
    let (_, _, _, branch, sibling) = fixture();
    let original = ResourceContext::new_with_equalities(&sibling)
        .unchecked_with_fact(coverage_piece(881_000, 0, 1));
    let alias = Address::symbolic(Variable(881_002));
    assert!(!original.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
    assert!(
        original
            .concrete_write_entries(&alias, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    let descendant = original
        .clone()
        .unchecked_with_fact(coverage_piece(881_003, 0, 1));
    let consumed = descendant
        .without_fact_incrementally(&coverage_piece(881_002, 0, 1), &branch)
        .unwrap();
    assert!(!consumed.satisfies_fact(&coverage_piece(881_002, 0, 1), &branch));
    assert!(consumed.satisfies_fact(&coverage_piece(881_003, 0, 1), &branch));
    assert_eq!(original.facts(), &[coverage_piece(881_000, 0, 1)]);
    assert!(!original.satisfies_fact(&coverage_piece(881_002, 0, 1), &sibling));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/memory_equality_index/projection_tests.rs");
}

#[test]
fn checked_composite_projection_keeps_the_point_of_a_bound_read() {
    use crate::kernel::borrows::CompositeProjectionEvidence;

    let _session = VerificationSession::enter();
    let slot = SymbolicMemory::global_pointer("projection_bound");
    let target = Address::symbolic(Variable(881_010));
    let typed = |pointer| ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer);
    let head = ResourceFact::view_composite(
        "point_projection".into(),
        vec![typed(slot.clone()), typed(target)],
    );
    let definition = CompositeResourceDefinition::new(
        "point_projection",
        vec![
            program_parameter("slot", ProgramType::Int32Pointer),
            program_parameter("target", ProgramType::Int32Pointer),
        ],
        None,
        false,
        vec![
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("slot"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            )),
            ResourceSpec::owned_memory(MemorySegment::new(
                crate::kernel::program_expression::variable("target"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::load(
                    crate::kernel::program_expression::variable("slot"),
                ),
            )),
        ],
        Vec::new(),
    );
    let state = ExecutionState::new().begin_function_entry_memory();
    let state = state
        .clone()
        .with_function_entry_memory(state.memory().clone().with_block(slot.base.clone(), 4));
    let point = state.program_point();
    let assumptions = PureFactContext::new();
    let definitions = std::slice::from_ref(&definition);
    let context = ResourceContext::new()
        .try_compose_with_fact(head.clone(), &assumptions)
        .expect("a single viewed composite");
    let (_, children, _) = crate::kernel::functions::expand_composite_resource_fact_with_children(
        &context,
        &head,
        definitions,
        &point,
        &assumptions,
    )
    .expect("the viewed body expands at the recorded point");
    assert!(children.iter().any(|child| {
        child.memory_range().is_some_and(|range| {
            matches!(range.end(), OldMachineTerm::MemoryLoad(at, address, LoadKind::Int32)
                if **address == slot && at.read_version_id() == point.id())
        })
    }));
    let expected = CompositeProjectionEvidence::from_checked_expansion(head.clone(), children)
        .expect("all checked children are views");
    let evidence = crate::kernel::functions::checked_composite_projection_evidence(
        &head,
        definitions,
        &point,
        &assumptions,
    )
    .expect("the projection recomputes the viewed body");
    assert_eq!(evidence, expected);
}
