use super::*;

#[test]
fn selected_root_goal_and_script_join_do_not_scan_other_obligations() {
    for size in [16_usize, 64, 256, 512] {
        let base = crate::kernel::api::contract_certification::contract_claims::contract_closing_tests::fixture();
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
        let entry = Arc::new(prepare_function_contract_entry_cases(
            program_function_contract_entry(&ExecutionState::new(), &function, &[]).unwrap(),
            ExecutionEnvironment::new().byte_order_fact(),
        ));
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

#[test]
fn completing_a_body_retires_only_its_own_declared_cell() {
    for size in [1usize, 16, 64, 256, 1024] {
        let (entry, execution) =
            crate::kernel::api::contract_certification::entry_authority_tests::checked_execution(
                0, None,
            )
            .unwrap();
        let function = entry.function.clone();
        let names = (0..size)
            .map(|index| format!("unrelated{index}"))
            .chain([function.name().to_string()])
            .collect::<BTreeSet<_>>();
        let program = crate::kernel::ProgramContractProof::open_ordinary(
            names.clone(),
            BTreeSet::new(),
            &BTreeSet::new(),
            &[&function],
            &[],
            names,
        )
        .unwrap();
        let root = WholeContractRoot::open_in_program(entry, &program.bodies()).unwrap();
        let attempt = root.begin_attempt();
        prove_strategy(attempt.root(), execution).publish(false);
        attempt.commit();
        let (body, work) =
            crate::instrumentation::measure_deterministic_work(|| root.finish().unwrap());
        assert!(work <= 96, "{size}: {work} body completion work");
        assert!(matches!(
            finish_program(program, body.termination_rule().clone()),
            Err(crate::kernel::ProgramContractFailure::UnfinishedBody(_))
        ));
    }
}
