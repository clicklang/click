use super::*;

#[test]
fn normal_evidence_completes_only_exhausted_void_function_source() {
    use crate::kernel::{CType, c_function};
    for (return_type, tail, region, completes) in [
        (CType::Void, false, ExecutionRegionKind::Function, true),
        (CType::Void, true, ExecutionRegionKind::Function, false),
        (CType::Int32, false, ExecutionRegionKind::Function, false),
        (CType::Void, false, ExecutionRegionKind::LoopBody, false),
        (CType::Void, false, ExecutionRegionKind::BranchArm, false),
    ] {
        let statement = CStatement::Skip;
        let body = if tail {
            CStatement::Seq(
                Arc::new(statement.clone()),
                Arc::new(CStatement::Return(CExpression::Value(CValue::Void))),
            )
        } else {
            statement.clone()
        };
        let function = c_function(return_type, "test", vec![], body);
        let mut core = ExecutionProofCore::at_entry(
            CState::new(),
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
