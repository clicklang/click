use super::*;

fn helper() -> CFunction {
    c_function(
        CType::Int32,
        "drain_to_zero",
        vec![c_parameter("n", CType::Int32)],
        c_seq(
            c_while(
                c_greater_than(c_variable("n"), c_int32_literal(0)),
                vec![],
                c_assign("n", c_subtract(c_variable("n"), c_int32_literal(1))),
            ),
            c_return(c_variable("n")),
        ),
    )
    .with_inline_body()
}

fn call(value: CValue, budget: &mut ExecutionBudget) -> ExecutionResult<Vec<CFunctionPath>> {
    let function = helper();
    execute_c_function_call_paths(
        &CState::new(),
        &function,
        &[CExpression::Value(value)],
        &PureFactContext::new(),
        CExecutionContext::new(
            &CExecutionEnvironment::new().with_function(function.clone()),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
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
        assert!(matches!(paths.as_slice(), [CFunctionPath {
                outcome: CFunctionOutcome::Return { value: CValue::Int32(value), .. }, ..
            }] if value.as_const() == Some(0)));
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
