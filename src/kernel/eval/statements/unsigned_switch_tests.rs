use super::*;

fn dispatch(
    selector: ProgramValue,
    cases: Vec<SwitchCase>,
    facts: &PureFactContext,
) -> StatementOutcome {
    execute_execution_statement(
        &ExecutionState::new(),
        &crate::kernel::program_switch(ProgramExpression::Value(selector), cases),
        facts,
    )
    .expect("established selector must choose one switch path")
}

fn returning_case(value: Option<u32>, result: u32) -> SwitchCase {
    SwitchCase {
        value,
        body: Box::new(ProgramStatement::Return(ProgramExpression::Value(int32(
            result,
        )))),
    }
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/eval/statements/unsigned_switch_tests.rs");
}
