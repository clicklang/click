use super::*;

#[test]
fn specification_execution_adapter_retains_growing_machine_results() {
    let mut work = Vec::new();
    for size in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut expression = sum(MachineIntegerType::UInt32);
        for _ in 1..size {
            expression = SpecExpression::Add(
                Box::new(expression),
                Box::new(SpecExpression::Value(ProgramValue::UInt32(
                    MachineTerm::Variable(Variable(998253)),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) =
            crate::instrumentation::measure_deterministic_work(|| adapter(&expression));
        assert_eq!(paths.len(), 1);
        let ExpressionOutcome::Value(SpecValue::Shared(root)) = &paths[0].outcome else {
            panic!("the adapter must retain the produced machine root");
        };
        assert_eq!(root.ty(), &KernelType::Program(ProgramType::UInt32));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn symbolic_integer_conversion_results_scale_with_the_selected_operand() {
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut source = IntegerTerm::Variable(Variable(999998));
        for _ in 0..size {
            source = IntegerTerm::Add(source.into(), IntegerTerm::constant_i64(1).into());
        }
        let expression = SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::Term(source)),
            destination: MachineIntegerType::Int32,
        };
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_expression_paths_with_loop_entry(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(paths[0].value.shared().is_some());
        assert_eq!(paths[0].obligations.len(), 2);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn specification_machine_expression_handoff_does_not_export_growing_results() {
    let mut work = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut source = ProgramExpression::Value(ProgramValue::UInt32(MachineTerm::Variable(
            Variable(999998),
        )));
        for _ in 0..size {
            source = ProgramExpression::Add(
                Box::new(source),
                Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::uint32_constant(1),
                ))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (paths, measured) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_expression_paths_with_loop_entry(
                &ExecutionState::new(),
                &SpecExpression::ProgramExpression(source),
                None,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(paths[0].value.shared().is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    assert!(
        work[0] > 0 && work[1] <= 5 * work[0] && work[2] <= 5 * work[1],
        "{work:?}"
    );
}

#[test]
fn boolean_lowering_keeps_growing_logical_results_shared() {
    let mut costs = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut condition = ConditionTerm::Variable(Variable(999991));
        for index in 0..size {
            condition = ConditionTerm::BoolIf {
                condition: Box::new(ConditionTerm::Variable(Variable(999000 + index))),
                then_condition: Box::new(condition),
                else_condition: Box::new(ConditionTerm::Constant(false)),
            };
        }
        let expression = SpecExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Bool(MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(condition),
            }),
        ));
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_spec_expression_paths_with_loop_entry(
                &ExecutionState::new(),
                &expression,
                None,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value.shared().unwrap().ty(), &KernelType::Bool);
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs[1] <= 5 * costs[0] && costs[2] <= 5 * costs[1],
        "{costs:?}"
    );
}

#[test]
fn algebraic_program_field_wrapping_does_not_walk_retained_prefixes() {
    let mut costs = Vec::new();
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut source = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Algebraic {
            name: "MatchScope".into(),
            arguments: vec![],
        }]);
        for _ in 0..size {
            source = AlgebraicTerm {
                algebraic_type: source.algebraic_type.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Arm".into(),
                    fields: vec![AlgebraicValue::Algebraic(source)],
                },
            };
        }
        // A program field's native carrier is declared before it is read.
        // Keep that registry context fixed: measure wrapping the retained
        // value, independently of first-time carrier admission.
        let _carrier = crate::kernel::TypeParameterName::of(&source.algebraic_type);
        let root = KernelTermImport::default().algebraic(&source);
        let exports = KernelTermExport::algebraic_export_count();
        let (field, work) = crate::instrumentation::measure_deterministic_work(|| {
            AlgebraicFieldResult::from_program(SpecValue::Shared(root.clone())).into_kernel()
        });
        assert!(
            matches!(field.node(), KernelTermNode::ProgramParameter { operand } if operand == &root)
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
        costs.push(work);
    }
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}
