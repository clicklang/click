use super::*;
use crate::kernel::VerificationSession;

#[test]
fn float_classification_lowering_preserves_native_selections_and_symbolic_calls() {
    let _session = VerificationSession::enter();
    let state = ExecutionState::new();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let lower = |source, native| {
            let mut execution = ExecutionBudget::new();
            let mut budget = SpecEvaluation::logical(&mut execution);
            budget.machine_result_production_disabled = native;
            let paths = lower_spec_float_classification_proposition_at_state_in(
                SpecScope::unbound(&state, None),
                &SpecExpression::Value(format.value(source)),
                FloatClassification::Zero,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap();
            let [path] = paths.as_slice() else {
                panic!("one classification path")
            };
            let Proposition::ConditionIs(condition, true) = &path.proposition else {
                panic!("expected a positive condition")
            };
            condition
                .root()
                .expect("shared classification output")
                .clone()
        };
        let zero = match format {
            KernelFloatType::Float32 => OldMachineTerm::uint32_constant(0x80000000),
            KernelFloatType::Float64 => OldMachineTerm::uint64_constant(0x8000000000000000),
        };
        let selection = OldMachineTerm::If {
            condition: Box::new(OldConditionTerm::Constant(true)),
            then_term: Box::new(zero),
            else_term: Box::new(OldMachineTerm::Variable(Variable(10993749))),
        };
        assert_eq!(
            lower(selection.clone(), true),
            KernelTerm::boolean_literal(true)
        );
        assert!(matches!(
            lower(selection, false).node(),
            KernelTermNode::FloatClassify { .. }
        ));

        let source = OldMachineTerm::ClickFunctionApplication {
            name: "classification_operand".into(),
            arguments: vec![PureFunctionArgument::Value(ProgramValue::UInt32(
                OldMachineTerm::uint32_constant(17),
            ))],
        };
        let condition = lower(source.clone(), true);
        assert_eq!(condition, lower(source.clone(), false));
        let expected = match format {
            KernelFloatType::Float32 => {
                OldConditionTerm::float32_classification(source, FloatClassification::Zero)
            }
            KernelFloatType::Float64 => {
                OldConditionTerm::float64_classification(source, FloatClassification::Zero)
            }
        };
        assert_eq!(KernelTermExport::condition(&condition).unwrap(), expected);
    }
}

#[test]
fn float_comparison_lowering_preserves_symbolic_operator_polarity() {
    let _session = VerificationSession::enter();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let left = OldMachineTerm::Variable(Variable(1008100));
        let right = OldMachineTerm::Variable(Variable(1008101));
        for operator in [
            ComparisonOperator::Equal,
            ComparisonOperator::NotEqual,
            ComparisonOperator::LessThan,
            ComparisonOperator::LessEqual,
            ComparisonOperator::GreaterThan,
            ComparisonOperator::GreaterEqual,
        ] {
            let condition = FloatCondition::Comparison {
                operator,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            };
            let condition = match format {
                KernelFloatType::Float32 => OldConditionTerm::Float32(condition),
                KernelFloatType::Float64 => OldConditionTerm::Float64(condition),
            };
            assert_eq!(
                program_value_comparison_proposition(
                    &format.value(left.clone()),
                    operator,
                    &format.value(right.clone())
                ),
                Some(Proposition::condition_is(condition, true))
            );
        }
    }
}

#[test]
fn float_inequality_lowering_preserves_ieee_constant_results() {
    let _session = VerificationSession::enter();
    for (format, one, two, negative_zero, nan) in [
        (
            KernelFloatType::Float32,
            0x3f800000,
            0x40000000,
            0x80000000,
            0x7fc00123,
        ),
        (
            KernelFloatType::Float64,
            0x3ff0000000000000,
            0x4000000000000000,
            0x8000000000000000,
            0x7ff8000000000123,
        ),
    ] {
        let value = |bits| {
            format.value(match format {
                KernelFloatType::Float32 => OldMachineTerm::constant(bits as u32),
                KernelFloatType::Float64 => OldMachineTerm::uint64_constant(bits),
            })
        };
        for (left, right, unequal) in [
            (one, one, false),
            (one, two, true),
            (0, negative_zero, false),
            (nan, nan, true),
            (nan, one, true),
            (one, nan, true),
        ] {
            for (operator, expected) in [
                (ComparisonOperator::NotEqual, unequal),
                (ComparisonOperator::Equal, !unequal),
            ] {
                assert_eq!(
                    program_value_comparison_proposition(&value(left), operator, &value(right)),
                    Some(Proposition::condition_is(
                        OldConditionTerm::Constant(expected),
                        true
                    )),
                    "{format:?}: {left:x} {operator:?} {right:x}"
                );
            }
        }
    }
}

#[test]
fn float_call_results_retain_nested_arguments_and_match_native_production() {
    let _session = VerificationSession::enter();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let call = |argument| SpecExpression::PureFunctionApplication {
            name: "float_step".into(),
            arguments: vec![SpecPureFunctionArgument::Value(argument)],
            result_type: format.program_type(),
            pointer_result: None,
            result_object_class: None,
        };
        let expression = call(call(SpecExpression::Value(
            format.value(OldMachineTerm::Variable(Variable(1008203))),
        )));
        let state = ExecutionState::new();
        let scope = SpecScope::unbound(&state, None);
        let exports = KernelTermExport::float_export_count();
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        let root = paths[0].value.shared().unwrap();
        assert!(matches!(root.node(), KernelTermNode::FloatCall(_)));
        assert!(matches!(
            root.children()[0].node(),
            KernelTermNode::FloatCall(_)
        ));
        assert_eq!(KernelTermExport::float_export_count(), exports);
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_result_production_disabled = true;
        let native = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .unwrap();
        assert_eq!(
            paths[0].value.clone().into_native(),
            native[0].value.clone().into_native()
        );
    }
}

#[test]
fn float_conditional_handoffs_preserve_exact_equality_and_existing_refusals() {
    let _session = VerificationSession::enter();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let root = KernelTerm::float_call(format, "float_branch".into(), vec![]);
        let left = SpecValue::Shared(root.clone());
        let native = SpecValue::Native(left.clone().into_native());
        let other = SpecValue::Shared(KernelTerm::float_call(
            format,
            "other_branch".into(),
            vec![],
        ));
        let condition = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        let exports = KernelTermExport::float_export_count();
        assert_eq!(
            SpecValue::conditional(&condition, &left, &native, true)
                .unwrap()
                .unwrap()
                .shared(),
            Some(&root)
        );
        assert!(
            SpecValue::conditional(&condition, &left, &other, true)
                .unwrap()
                .is_none()
        );
        assert_eq!(KernelTermExport::float_export_count(), exports);
        assert!(
            SpecValue::conditional(&condition, &left, &other, false)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn float_specification_values_and_program_reads_keep_execution_roots() {
    let _session = VerificationSession::enter();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let root = KernelTerm::float_call(format, "float_local".into(), vec![]);
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "x",
            SpecValue::Shared(root.clone()),
            format.program_type(),
            false,
            false,
            false,
            false,
        );
        let exports = KernelTermExport::float_export_count();
        let expression = SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&state, None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        assert_eq!(paths[0].value.shared(), Some(&root));
        assert_eq!(KernelTermExport::float_export_count(), exports);
        let expression =
            SpecExpression::Value(format.value(OldMachineTerm::Variable(Variable(1008300))));
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&state, None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::new()),
        )
        .unwrap();
        assert!(paths[0].value.shared().is_some());
    }
}
