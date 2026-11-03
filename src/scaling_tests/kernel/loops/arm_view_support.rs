use super::*;

#[test]
fn republished_arm_view_keeps_support_at_growing_context_sizes() {
    let mut costs = Vec::new();
    for size in [1, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let range = CMemoryRange::new(
            Pointer::symbolic(Variable(8_390_080)),
            Bitvector32Term::constant(0),
            Bitvector32Term::constant(1),
        );
        let owner = CResourceFact::own_memory(range.clone());
        let view = CResourceFact::view_memory(range);
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(owner.clone())
            .unchecked_with_supported_facts(&owner, std::iter::repeat_n(view.clone(), size));
        for index in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::own(CResource::Token {
                name: format!("unrelated-{index}"),
                arguments: vec![].into(),
            }));
        }
        let before = resources.facts().len();
        let state = CState::new().with_resource_context(resources);
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_arm_views_preserving_support(&state, vec![view.clone()])
        });
        costs.push(work);
        assert_eq!(after.resources().facts().len(), before);
        assert!(after.resources().exact_projection_support(&view).is_some());
        let consumed = after
            .resources()
            .clone()
            .without_fact(&owner, &PureFactContext::new())
            .expect("consume the supporting owner");
        assert!(!consumed.contains_exact_representation(&view));
    }
    assert!(costs[0] > 0);
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
