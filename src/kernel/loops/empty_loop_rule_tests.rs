use super::*;

/// A genuinely unannotated loop without a checked rule must retain the
/// evaluator's unrolling bound, even though rule dispatch checks all loops.
#[test]
fn unannotated_loop_without_rule_keeps_unrolling_bound() {
    let statement = c_while(c_int32_literal(1), Vec::new(), CStatement::Skip);
    let mut budget = ExecutionBudget::default().with_loop_unrolls(0);
    let (execution, rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            CState::new(),
            statement,
            PureFactContext::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    assert_eq!(execution.limit, Some(ExecutionLimit::LoopUnrolls));
    assert!(rule.is_none());
}
