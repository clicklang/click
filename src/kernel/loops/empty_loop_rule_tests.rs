use super::*;

/// A genuinely unannotated loop without a checked rule must retain the
/// evaluator's unrolling bound, even though rule dispatch checks all loops.
#[test]
fn unannotated_loop_without_rule_keeps_unrolling_bound() {
    let statement = program_while(
        crate::kernel::program_expression::int32_literal(1),
        Vec::new(),
        ProgramStatement::Skip,
    );
    let mut budget = ExecutionBudget::default().with_loop_unrolls(0);
    let (execution, rule) =
        prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            ExecutionState::new(),
            statement,
            PureFactContext::new(),
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    assert_eq!(execution.limit, Some(ExecutionLimit::LoopUnrolls));
    assert!(rule.is_none());
}
