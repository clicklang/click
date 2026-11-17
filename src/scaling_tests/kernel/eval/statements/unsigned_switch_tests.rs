// Scaling tests of `src/kernel/eval/statements/unsigned_switch_tests.rs`:
// dispatch costs explicit cases, independently of unrelated and alias facts.

#[test]
fn unsigned_switch_dispatch_does_not_scan_unrelated_or_alias_facts() {
    for aliases in [false, true] {
        for selected in [0u32, u32::MAX] {
            let mut costs = Vec::new();
            for size in [0, 32, 128] {
                let _session = crate::kernel::VerificationSession::enter();
                let selector = MachineTerm::Variable(Variable(996_001));
                let mut facts = PureFactContext::new().assume_condition(
                    ConditionTerm::uint32_equal(
                        selector.clone(),
                        MachineTerm::uint32_constant(selected),
                    ),
                    true,
                );
                for index in 0..size {
                    facts = facts.assume_condition(
                        ConditionTerm::uint32_equal(
                            MachineTerm::Variable(Variable(997_000 + index)),
                            if aliases {
                                selector.clone()
                            } else {
                                MachineTerm::uint32_constant(index as u32)
                            },
                        ),
                        true,
                    );
                }
                let cases = vec![returning_case(Some(0), 1), returning_case(None, 2)];
                let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                    dispatch(ProgramValue::UInt32(selector), cases, &facts)
                });
                assert!(matches!(outcome,
                    StatementOutcome::Return { value, .. }
                        if value.matches_native(&int32(if selected == 0 { 1 } else { 2 }))));
                costs.push(work);
            }
            assert!(
                costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 64),
                "aliases={aliases}, selected={selected}: {costs:?}"
            );
        }
    }
}

#[test]
fn unsigned_switch_dispatch_work_tracks_explicit_cases() {
    let mut costs = Vec::new();
    for count in [4u32, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut cases = (0..count)
            .map(|value| returning_case(Some(value), 0))
            .collect::<Vec<_>>();
        cases.push(returning_case(None, 777));
        let facts = PureFactContext::new();
        let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
            dispatch(
                ProgramValue::UInt32(MachineTerm::uint32_constant(u32::MAX)),
                cases,
                &facts,
            )
        });
        assert!(matches!(outcome,
            StatementOutcome::Return { value, .. }
                if value.matches_native(&int32(777))));
        costs.push((count, work));
    }
    let (_, base) = costs[0];
    assert!(
        base > 0
            && costs
                .iter()
                .all(|(count, work)| *work <= base * *count as usize / 4 * 2),
        "{costs:?}"
    );
}
