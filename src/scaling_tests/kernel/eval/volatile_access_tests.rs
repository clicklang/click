use super::*;

#[test]
fn typed_volatile_events_scale_with_new_accesses_and_share_forked_history() {
    let mut creation = Vec::new();
    let mut selected = Vec::new();
    for size in [16usize, 64, 256, 1024] {
        let mut budget = ExecutionBudget::default();
        let mut facts = ExecutionFacts::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let kind = if index % 2 == 0 {
                    VolatileAccessKind::Read
                } else {
                    VolatileAccessKind::Write
                };
                facts.push(access(&mut budget, kind));
            }
        });
        creation.push(work);
        let branch = facts.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let read = access(&mut budget, VolatileAccessKind::Read);
            assert!(read.volatile_read_result().is_some());
            facts.push(read);
        });
        selected.push(work);
        assert_eq!(facts.len(), size + 1);
        assert_eq!(branch.len(), size);
        let ids = branch
            .iter()
            .map(|fact| {
                let Proposition::VolatileAccess(event) = fact.proposition() else {
                    panic!()
                };
                event.id
            })
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(ids.len(), size);
    }
    assert!(creation.iter().all(|work| *work > 0));
    assert!(
        creation.windows(2).all(|pair| pair[1] <= pair[0] * 5 + 32),
        "{creation:?}"
    );
    assert!(
        selected.iter().all(|work| *work == selected[0]),
        "{selected:?}"
    );
}
