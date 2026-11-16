use super::*;

#[test]
fn selecting_head_locals_does_not_scan_the_entry_environment() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut costs = Vec::new();
    for count in [16, 64, 256, 1024] {
        let mut entry = ExecutionState::new().with_local("selected", int32(0));
        for index in 0..count {
            entry = entry.with_local(format!("other{index}"), int32(index));
        }
        let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
        let mut budget = ExecutionBudget::default();
        let (description, work) = crate::persistent::measure_persistent_work(|| {
            LoopHeadLocals::new(
                &entry,
                BTreeSet::from(["selected".into()]),
                &mut variables,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(description.values.len(), 1);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= 3 * costs[0]),
        "loop-head local selection: {costs:?}"
    );
}
