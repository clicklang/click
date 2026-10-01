use super::*;
use crate::kernel::*;

// Observe only this test's actual projection input, with no production hook
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
    head: &CResourceFact,
    definition: &CCompositeResourceDefinition,
    memory: &CMemory,
    facts: &PureFactContext,
) -> ResourceContext {
    struct Restore(Option<Option<ResourceContext>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OBSERVED_CONTEXT.with(|cell| *cell.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(OBSERVED_CONTEXT.with(|cell| cell.replace(Some(None))));
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            head,
            std::slice::from_ref(definition),
            memory,
            facts,
        )
        .is_some(),
        "the viewed body must expand"
    );
    OBSERVED_CONTEXT.with(|cell| cell.borrow_mut().as_mut().unwrap().take().unwrap())
}

fn prior_child(context: ResourceContext, head: &CResourceFact) -> ResourceContext {
    let child = CResourceFact::own_memory(CMemoryRange::new(
        Pointer::symbolic(Variable(881_000)),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    context
        .without_exact_representation(head)
        .unwrap()
        .unchecked_with_fact(child)
}

fn fixture() -> (
    CResourceFact,
    CCompositeResourceDefinition,
    CMemory,
    PureFactContext,
    PureFactContext,
) {
    let at = |id| Pointer::symbolic(Variable(id));
    let (slot, middle, alias, target) = (at(881_000), at(881_001), at(881_002), at(881_003));
    let typed = |pointer| CValue::typed_pointer(pointer, CType::Int32Pointer);
    let head = CResourceFact::view_composite(
        "dependent_projection".into(),
        vec![
            typed(slot.clone()),
            typed(alias.clone()),
            typed(target.clone()),
        ],
    );
    let definition = CCompositeResourceDefinition::new(
        "dependent_projection",
        vec![
            c_parameter("slot", CType::Int32Pointer),
            c_parameter("alias", CType::Int32Pointer),
            c_parameter("target", CType::Int32Pointer),
        ],
        None,
        false,
        vec![
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("slot"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("target"),
                c_int32_literal(0),
                c_load(c_variable("alias")),
            )),
        ],
        Vec::new(),
    );
    let memory = CMemory::new()
        .with_block(slot.block.clone(), 4)
        .with_block(target.block, 8)
        .store(slot.clone(), int32(2u32));
    let sibling = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(882_000)),
                Bitvector32Term::Variable(Variable(882_001)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(slot, middle.clone()), true);
    let branch = sibling
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(middle, alias), true);
    (head, definition, memory, branch, sibling)
}

#[test]
fn dependent_composite_projection_selects_the_prior_child_by_graph_address() {
    let (head, definition, memory, branch, sibling) = fixture();
    // Logical loads may bypass permission checks, so successful expansion
    // alone cannot establish that its resource index follows the graph.
    let context = projection_context(&head, &definition, &memory, &branch);
    let children = prior_child(context, &head);
    let alias = Pointer::symbolic(Variable(881_002));
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
    assert!(sibling_children.facts().iter().all(CResourceFact::is_own));
}

#[test]
fn projection_evidence_still_requires_a_viewed_head_and_matching_definition() {
    let (head, definition, memory, facts, _) = fixture();
    let owned = CResourceFact::own(head.resource().clone());
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &owned,
            std::slice::from_ref(&definition),
            &memory,
            &facts,
        )
        .is_none()
    );
    assert!(
        crate::kernel::functions::checked_composite_projection_evidence(
            &head,
            &[],
            &memory,
            &facts,
        )
        .is_none()
    );
}

#[test]
fn projection_context_attachment_does_not_scan_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (head, definition, memory, mut facts, _) = fixture();
        for i in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(890_000 + i * 2)),
                    Bitvector32Term::Variable(Variable(890_001 + i * 2)),
                ),
                true,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let context = projection_context(&head, &definition, &memory, &facts);
                let children = prior_child(context, &head);
                let alias = Pointer::symbolic(Variable(881_002));
                assert!(
                    children
                        .concrete_read_entries(&alias, 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(children.permits_memory_read(&alias, 4, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "projection scanned unrelated facts: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "projection rebuilt unrelated graph state: {samples:?}"
    );
}
