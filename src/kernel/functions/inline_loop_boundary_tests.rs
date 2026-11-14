use super::*;

fn helper() -> ProgramFunction {
    program_function(
        ProgramType::Int32,
        "drain_to_zero",
        vec![program_parameter("n", ProgramType::Int32)],
        program_seq(
            program_while(
                crate::kernel::program_expression::greater_than(
                    crate::kernel::program_expression::variable("n"),
                    crate::kernel::program_expression::int32_literal(0),
                ),
                vec![],
                program_assign(
                    "n",
                    crate::kernel::program_expression::subtract(
                        crate::kernel::program_expression::variable("n"),
                        crate::kernel::program_expression::int32_literal(1),
                    ),
                ),
            ),
            program_return(crate::kernel::program_expression::variable("n")),
        ),
    )
    .with_inline_body()
}

fn call(value: ProgramValue, budget: &mut ExecutionBudget) -> ExecutionResult<Vec<FunctionPath>> {
    let function = helper();
    execute_program_function_call_paths(
        &ExecutionState::new(),
        &function,
        &[ProgramExpression::Value(value)],
        &PureFactContext::new(),
        ExecutionContext::new(
            &ExecutionEnvironment::new().with_function(function.clone()),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
        ),
        budget,
    )
}

#[test]
fn concrete_inline_loops_still_unroll_and_restore_the_call_context_on_error() {
    let _session = crate::kernel::VerificationSession::enter();
    for count in [0, 4, 16, 64] {
        let mut budget = ExecutionBudget::new();
        let paths = call(int32(count), &mut budget).unwrap();
        assert!(matches!(paths.as_slice(), [FunctionPath {
                outcome: FunctionOutcome::Return { value, .. }, ..
            }] if matches!(value.native().as_ref(), ProgramValue::Int32(bits) if bits.as_const() == Some(0))));
        assert!(budget.inline_call_name.is_none());
    }
    let mut budget = ExecutionBudget::new();
    budget.loop_unrolls = 0;
    budget.inline_call_name = Some("outer".into());
    assert_eq!(
        call(int32(4), &mut budget),
        Err(ExecutionLimit::LoopUnrolls)
    );
    assert_eq!(budget.inline_call_name.as_deref(), Some("outer"));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/inline_loop_boundary_tests.rs");
}
