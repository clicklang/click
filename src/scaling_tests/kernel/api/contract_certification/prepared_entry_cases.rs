use super::*;

#[test]
fn retained_entry_cases_are_reused_without_reenumeration_or_unrelated_fact_walks() {
    for guards in [1_usize, 2, 3, 4] {
        let mut expected_work = None;
        for unrelated in [0, 64, 256] {
            let (state, function, arguments) = fixture(guards, unrelated);
            let opened = crate::kernel::proof::OpenedContractEntry::open(
                &state,
                &function,
                &arguments,
                &Vec::<Proposition>::new(),
                &ExecutionEnvironment::new(),
            )
            .unwrap();
            let prepared = opened.prepared_cases();
            assert_eq!(prepared.case_count(), 1 << guards);
            let before = guard_case_builds();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                prove_prepared_function_contract_execution_paths(
                    prepared,
                    function.clone(),
                    ExecutionEnvironment::new(),
                    ExecutionSemantics::APPLY_VERIFIED_RULES,
                    FunctionContractExecutionMode::VerifyLoops,
                    &[],
                    &[],
                )
            });
            assert_eq!(guard_case_builds(), before);
            if let Some(expected) = expected_work {
                assert_eq!(
                    work, expected,
                    "{guards} guards, {unrelated} unrelated requirements"
                );
            } else {
                expected_work = Some(work);
            }
            assert!(
                work <= 256 * (guards + 1) * (1 << guards),
                "{guards} guards: {work}"
            );
        }
    }
}
