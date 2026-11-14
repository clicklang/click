use super::*;

#[test]
fn whole_contract_retirement_is_indexed_and_preserves_candidate_forks() {
    for clauses in [16_usize, 64, 256, 512] {
        for unrelated in [0, 256] {
            let (base, _) = contract_closing_tests::fixture(1);
            let ensure = base.contract_ensures()[0].clone();
            let function = base.with_contract(
                (0..unrelated)
                    .map(|index| SpecProposition::Predicate {
                        name: format!("unrelated_{index}"),
                        arguments: vec![],
                        resource_state_dependent: false,
                    })
                    .collect(),
                vec![ensure; clauses],
                vec![],
                (0..clauses)
                    .map(|index| FunctionContractClaim::ensure_proposition(index, index))
                    .collect(),
                true,
            );
            let entry = prepare_function_contract_entry_cases(
                program_function_contract_entry(&ExecutionState::new(), &function, &[]).unwrap(),
                ExecutionEnvironment::new().byte_order_fact(),
            )
            .unwrap();
            let original = WholeContractProof::open(Arc::new(entry)).unwrap();
            let ((closed, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut candidate = original.clone();
                    for index in (0..clauses).rev() {
                        candidate.retire(ContractCompletionGoal::Claim {
                            case: 0,
                            key: FunctionContractClaimKey::Ensure(index),
                        });
                        assert_eq!(
                            candidate.first_open(),
                            Some(ContractCompletionGoal::Boundary { case: 0 })
                        );
                    }
                    candidate.retire(ContractCompletionGoal::Boundary { case: 0 });
                    candidate
                })
            });
            assert!(closed.first_open().is_none());
            assert_eq!(original.open.len(), clauses + 1);
            assert!(
                work <= 4 * clauses + 4,
                "{clauses} clauses, {unrelated} unrelated requirements: {work}"
            );
            assert!(
                indexed_work <= 32 * clauses * (clauses.ilog2() as usize + 1),
                "{clauses} clauses, {unrelated} unrelated requirements: {indexed_work} index visits"
            );
        }
    }
}
