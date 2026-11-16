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

#[test]
fn boolean_lowering_preserves_logical_roots_and_exact_c_carriers() {
    let _session = crate::kernel::VerificationSession::enter();
    let condition = ConditionTerm::Variable(Variable(999991));
    let cases = [
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 0,
            },
            true,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 1,
            },
            true,
        ),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(condition),
            },
            true,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 2,
            },
            false,
        ),
        (
            MachineTerm::Constant {
                format: MachineIntegerType::UInt32,
                bits: 1,
            },
            false,
        ),
        (MachineTerm::Variable(Variable(999992)), false),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(ConditionTerm::Constant(true)),
            },
            false,
        ),
        (
            MachineTerm::BoolCast {
                to: MachineIntegerType::UInt32,
                value: Box::new(ConditionTerm::Variable(Variable(999993))),
            },
            false,
        ),
    ];
    for (word, logical) in cases {
        // The C evaluator rejects malformed Bool values before this handoff.
        // Specification payloads must still preserve those exact carriers.
        let valid_c_value = matches!(
            &word,
            MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 0 | 1
            } | MachineTerm::Variable(_)
                | MachineTerm::BoolCast {
                    to: MachineIntegerType::UInt8,
                    ..
                }
        );
        let value = ProgramValue::Bool(word);
        let mut expressions = vec![SpecExpression::Value(value.clone())];
        if valid_c_value {
            expressions.push(SpecExpression::ProgramExpression(ProgramExpression::Value(
                value.clone(),
            )));
        }
        for expression in expressions {
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
            let retained = evaluate(false);
            let native = evaluate(true);
            assert_eq!(retained.value.shared().is_some(), logical, "{value:?}");
            if logical {
                let expected = KernelTermImport::default()
                    .argument(&PureFunctionArgument::Value(value.clone()));
                assert_eq!(retained.value.shared(), Some(&expected));
            }
            assert!(native.value.shared().is_none());
            assert_eq!(retained.facts, native.facts);
            assert_eq!(retained.obligations, native.obligations);
            assert_eq!(retained.value.into_native(), value);
            assert_eq!(native.value.into_native(), value);
        }
    }
}

#[test]
fn algebraic_lowering_retains_program_envelopes_and_handoff_roots() {
    let _session = crate::kernel::VerificationSession::enter();
    for native in [
        KernelMatch::test_scrutinee(vec![]),
        AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("T".into()),
            node: AlgebraicTermNode::Variable(Variable(999994)),
        },
    ] {
        let root = KernelTermImport::default().algebraic(&native);
        let program_type = ProgramType::Parameter(TypeParameterName::of(&native.algebraic_type));
        let expected = AlgebraicValue::Program(ProgramValue::Parameter(Box::new(native.clone())));
        let exports = KernelTermExport::algebraic_export_count();
        let field = AlgebraicFieldResult::from_program(SpecValue::Shared(root.clone()));
        assert!(field.has_type(&AlgebraicValueType::Program(program_type)));
        assert!(!field.has_type(&native.algebraic_type.value_type()));
        let envelope = field.clone().into_kernel();
        assert!(
            matches!(envelope.node(), KernelTermNode::ProgramParameter { operand } if operand == &root)
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        assert_eq!(field.into_native(), expected);
        assert_eq!(
            AlgebraicFieldResult::from_program(SpecValue::Shared(envelope.clone())).into_kernel(),
            envelope
        );
        assert_eq!(
            AlgebraicFieldResult::from_algebraic(AlgebraicResult::Shared(root.clone()))
                .into_kernel(),
            root
        );
        {
            let stored = root;
            let mut state = ExecutionState::new();
            state.locals.set_retained_typed_with_all_qualifiers(
                "value",
                SpecValue::Shared(stored.clone()),
                program_type,
                false,
                false,
                false,
                false,
            );
            let expression =
                SpecExpression::ProgramExpression(ProgramExpression::Variable("value".into()));
            let evaluate = |disabled| {
                let mut budget = ExecutionBudget::new();
                let mut evaluation = SpecEvaluation::logical(&mut budget);
                evaluation.machine_result_production_disabled = disabled;
                evaluate_spec_expression_paths_with_bindings_in(
                    &state,
                    &expression,
                    &PureFactContext::new(),
                    &BTreeMap::new(),
                    &mut evaluation,
                )
                .unwrap()
                .pop()
                .unwrap()
            };
            let exports = KernelTermExport::algebraic_export_count();
            let actual = evaluate(false);
            assert_eq!(actual.value.shared(), Some(&stored));
            assert_eq!(KernelTermExport::algebraic_export_count(), exports);
            let old = evaluate(true);
            assert_eq!(actual.facts, old.facts);
            assert_eq!(actual.obligations, old.obligations);
            assert_eq!(actual.value.into_native(), old.value.into_native());
        }
    }
}
