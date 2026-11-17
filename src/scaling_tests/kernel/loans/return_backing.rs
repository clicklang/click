use super::*;
#[test]
fn selected_permissions_ignore_related_projection_history() {
    let p = Pointer::symbolic(Variable(8_911_000));
    let view = |start: u32| {
        ResourceFact::view_memory(MemoryRange::new(
            p.clone(),
            start.into(),
            (start + 1).into(),
        ))
    };
    let mut samples = Vec::new();
    for count in [4u32, 16, 64] {
        let permissions: PermittedDescriptions = (0..count).map(|index| view(index * 2)).collect();
        let selected = view(0);
        let missing = view(9999);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let _fast =
                crate::kernel::search::FastOperationScope::enter("selected loan permission");
            assert_eq!(permissions.candidate(&selected), Some(&selected));
            assert!(permissions.candidate(&missing).is_none());
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
