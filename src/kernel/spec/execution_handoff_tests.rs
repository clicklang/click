use super::*;

fn adapter(expression: &SpecExpression) -> Vec<ExpressionPath<SpecValue>> {
    evaluate_resource_child_argument_paths(
        &ExecutionState::new(),
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
            &ExecutionState::new(),
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
            assert_eq!(actual.outcome, ExpressionOutcome::Value(expected.value));
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
fn program_expression_handoff_preserves_values_and_errors() {
    let _session = crate::kernel::VerificationSession::enter();
    for expression in [
        ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::uint32_constant(7))),
        ProgramExpression::Variable("missing".into()),
        ProgramExpression::Divide(
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(1),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(0),
            ))),
        ),
    ] {
        let expected = {
            let _scope = crate::kernel::eval::SpecificationReadScope::enter();
            evaluate_program_expression_paths(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        };
        let actual = adapter(&SpecExpression::ProgramExpression(expression));
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

#[test]
fn symbolic_integer_conversions_produce_shared_roots_with_the_same_bounds() {
    let _session = crate::kernel::VerificationSession::enter();
    for destination in [
        MachineIntegerType::Int8,
        MachineIntegerType::UInt8,
        MachineIntegerType::Int16,
        MachineIntegerType::UInt16,
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
        MachineIntegerType::Int128,
        MachineIntegerType::UInt128,
    ] {
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(IntegerTerm::Variable(
                Variable(999996),
            ))),
            destination,
        };
        let evaluate = |disabled| {
            let mut budget = ExecutionBudget::new();
            let mut evaluation = SpecEvaluation::logical(&mut budget);
            evaluation.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &BTreeMap::new(),
                &mut evaluation,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let native = evaluate(true);
        let exports = KernelTermExport::machine_export_count();
        let retained = evaluate(false);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let root = retained.value.shared().expect("retained conversion");
        assert!(
            matches!(root.node(), KernelTermNode::IntegerToMachine { destination: actual, .. } if *actual == destination)
        );
        assert_eq!(retained.facts, native.facts);
        assert_eq!(retained.obligations, native.obligations);
        assert!(!retained.obligations.is_empty());
        assert_eq!(retained.value.into_native(), native.value.into_native());
    }
}

#[test]
fn specification_machine_expression_handoff_keeps_the_execution_root() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let source = ProgramExpression::Add(
            Box::new(ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(999997))),
            )),
            Box::new(ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(999998))),
            )),
        );
        let state = ExecutionState::new();
        let assumptions = PureFactContext::new();
        let expected = {
            let _scope = crate::kernel::eval::SpecificationReadScope::enter();
            evaluate_expression_value_paths(
                &state,
                &source,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap()
            .into_iter()
            .find(|path| matches!(path.outcome, ExpressionOutcome::Value(_)))
            .expect("the defined execution path")
        };
        let ExpressionOutcome::Value(expected_value) = expected.outcome else {
            panic!()
        };
        assert!(expected_value.shared().is_some());
        let expression = SpecExpression::ProgramExpression(source);
        let evaluate = |disabled| {
            let mut budget = ExecutionBudget::new();
            let mut evaluation = SpecEvaluation::logical(&mut budget);
            evaluation.machine_result_production_disabled = disabled;
            evaluate_spec_expression_paths_with_bindings_in(
                &state,
                &expression,
                &assumptions,
                &BTreeMap::new(),
                &mut evaluation,
            )
            .unwrap()
            .pop()
            .unwrap()
        };
        let exports = KernelTermExport::machine_export_count();
        let actual = evaluate(false);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(actual.value.shared(), expected_value.shared());
        assert_eq!(actual.obligations, expected.obligations);
        assert_eq!(actual.facts, expected.facts);
        let native = evaluate(true);
        assert!(native.value.shared().is_none());
        assert_eq!(actual.obligations, native.obligations);
        assert_eq!(actual.facts, native.facts);
        assert_eq!(actual.value.into_native(), native.value.into_native());
    }
}
