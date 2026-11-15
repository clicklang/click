use super::*;

#[test]
fn selected_root_goal_and_script_join_do_not_scan_other_obligations() {
    for size in [16_usize, 64, 256, 512] {
        let (base, _) = crate::kernel::api::contract_certification::contract_claims::contract_closing_tests::fixture(1);
        let ensure = base.contract_ensures()[0].clone();
        let function = base.with_contract(
            vec![],
            vec![ensure; size],
            vec![],
            (0..size)
                .map(|i| FunctionContractClaim::ensure_proposition(i, i))
                .collect(),
            true,
        );
        let entry = Arc::new(
            prepare_function_contract_entry_cases(
                program_function_contract_entry(&ExecutionState::new(), &function, &[]).unwrap(),
                ExecutionEnvironment::new().byte_order_fact(),
            )
            .unwrap(),
        );
        let root = WholeContractRoot::open(entry).unwrap();
        let selected = ContractCompletionGoal::Claim {
            case: 0,
            key: FunctionContractClaimKey::Ensure(size - 1),
        };
        let (((), work), indexed) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let attempt = root.begin_attempt();
                {
                    let mut state = attempt.root.state.lock().unwrap();
                    let state = state.as_mut().unwrap();
                    assert!(state.goal.retire(selected.clone()));
                    state.closed.insert(selected.clone(), ());
                }
                attempt.commit();
            })
        });
        let state = root.state.lock().unwrap();
        let state = state.as_ref().unwrap();
        assert_eq!(state.goal.open.len(), size);
        assert_eq!(state.closed.len(), 1);
        assert!(work <= 8, "{size} clauses: {work} work");
        assert!(
            indexed <= 128 * (size.ilog2() as usize + 1),
            "{size} clauses: {indexed} index visits"
        );
        assert!(state.goal.first_open().is_some());
    }
}
