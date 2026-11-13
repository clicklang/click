use super::*;

fn adapter(expression: &SpecExpression) -> Vec<CExpressionPath<SpecValue>> {
    evaluate_resource_child_argument_paths(
        &CState::new(),
        expression,
        &PureFactContext::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut ExecutionBudget::new(),
    )
    .unwrap()
}

fn sum(format: MachineIntegerType) -> SpecExpression {
    SpecExpression::Add(
        Box::new(SpecExpression::Value(
            format.value_from_term(MachineTerm::Variable(Variable(998252))),
        )),
        Box::new(SpecExpression::Value(format.value_from_term(
            match format {
                MachineIntegerType::Int32 => MachineTerm::constant(1),
                MachineIntegerType::UInt32 => MachineTerm::uint32_constant(1),
                MachineIntegerType::Int64 => MachineTerm::int64_constant(1),
                MachineIntegerType::UInt64 => MachineTerm::uint64_constant(1),
                _ => unreachable!(),
            },
        ))),
    )
}

#[test]
fn specification_execution_handoff_keeps_the_produced_root_and_debts() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let expression = sum(format);
        let mut budget = ExecutionBudget::new();
        let expected = evaluate_spec_expression_paths_with_bindings_in(
            &CState::new(),
            &expression,
            &PureFactContext::new(),
            &BTreeMap::new(),
            &mut SpecEvaluation::checked(&mut budget),
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let actual = adapter(&expression);
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert!(matches!(expected.value, SpecValue::Shared(_)));
            assert_eq!(actual.outcome, CExpressionOutcome::Value(expected.value));
            assert_eq!(actual.facts, expected.facts);
            assert_eq!(actual.obligations, expected.obligations);
            if format.format().is_signed() {
                assert!(!actual.obligations.is_empty());
            }
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[test]
fn c_fragment_handoff_preserves_values_and_errors() {
    let _session = crate::kernel::VerificationSession::enter();
    for expression in [
        CExpression::Value(CValue::UInt32(MachineTerm::uint32_constant(7))),
        CExpression::Variable("missing".into()),
        CExpression::Divide(
            Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(1)))),
            Box::new(CExpression::Value(CValue::Int32(MachineTerm::constant(0)))),
        ),
    ] {
        let expected = {
            let _scope = crate::kernel::eval::SpecificationReadScope::enter();
            evaluate_c_expression_paths(
                &CState::new(),
                &expression,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        };
        let actual = adapter(&SpecExpression::CExpression(expression));
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.into_iter().zip(expected) {
            assert_eq!(
                actual.outcome.map_value(SpecValue::into_native),
                expected.outcome
            );
            assert_eq!(actual.facts, expected.facts);
            assert_eq!(actual.obligations, expected.obligations);
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/execution_handoff_tests.rs");
}
