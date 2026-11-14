use super::*;

#[test]
fn normal_evidence_completes_only_exhausted_void_function_source() {
    use crate::kernel::{ProgramType, c_function};
    for (return_type, tail, region, completes) in [
        (
            ProgramType::Void,
            false,
            ExecutionRegionKind::Function,
            true,
        ),
        (
            ProgramType::Void,
            true,
            ExecutionRegionKind::Function,
            false,
        ),
        (
            ProgramType::Int32,
            false,
            ExecutionRegionKind::Function,
            false,
        ),
        (
            ProgramType::Void,
            false,
            ExecutionRegionKind::LoopBody,
            false,
        ),
        (
            ProgramType::Void,
            false,
            ExecutionRegionKind::BranchArm,
            false,
        ),
    ] {
        let statement = ProgramStatement::Skip;
        let body = if tail {
            ProgramStatement::seq(
                Arc::new(statement.clone()),
                Arc::new(ProgramStatement::Return(ProgramExpression::Value(
                    ProgramValue::Void,
                ))),
            )
        } else {
            statement.clone()
        };
        let function = c_function(return_type, "test", vec![], body);
        let mut core = ExecutionProofCore::at_entry(
            ExecutionState::new(),
            ExecutionFrontier {
                region,
                ..ExecutionFrontier::default()
            },
        );
        let before = core.running_state(&function, &[]).unwrap().into_owned();
        let theorem = Theorem::new(Proposition::CStatementVerifies {
            state: Box::new(before.clone()),
            statement: Box::new(statement),
            outcome: CStatementOutcome::Normal(Box::new(before)),
        });
        core.record_statement_transition(
            &function,
            &[],
            theorem,
            PureFactContext::new(),
            &ExecutionFacts::new(),
            &[],
        )
        .unwrap();
        assert_eq!(core.evidence_completed, completes);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/checked_callee_dependency_tests.rs");
}
