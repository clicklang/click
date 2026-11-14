use super::*;
use crate::kernel::VerificationSession;
const FORMATS: [MachineIntegerType; 8] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
];
fn call(format: MachineIntegerType, name: &str) -> KernelTerm {
    let application = SharedPureApplication::intern(
        name.into(),
        vec![PureFunctionArgument::Value(ProgramValue::Int32(
            MachineTerm::Variable(Variable(995810)),
        ))],
    );
    KernelTermImport::default().machine_call(format, &application)
}
// Oracle-only materialization: argument carrier choice is not a change to
// the call's typed value. Production readers keep these handles retained.
fn native_term(value: &MachineTerm) -> MachineTerm {
    match value {
        MachineTerm::ClickFunctionApplication { name, arguments } => {
            MachineTerm::ClickFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|arg| match arg {
                        PureFunctionArgument::SharedMachine(value) => PureFunctionArgument::Value(
                            value.ty().value_from_term(native_term(value.value())),
                        ),
                        PureFunctionArgument::Value(value) => {
                            if let crate::kernel::integer_c_value!(term) = value {
                                PureFunctionArgument::Value(
                                    MachineIntegerType::from_program_type(value.program_type())
                                        .unwrap()
                                        .value_from_term(native_term(term)),
                                )
                            } else {
                                arg.clone()
                            }
                        }
                        arg => arg.clone(),
                    })
                    .collect(),
            }
        }
        MachineTerm::Cast {
            spelling,
            from,
            to,
            value,
        } => MachineTerm::Cast {
            spelling: *spelling,
            from: *from,
            to: *to,
            value: Box::new(native_term(value)),
        },
        value => value.clone(),
    }
}
fn native_integer(value: &SharedIntegerTerm) -> IntegerTerm {
    match value.as_ref() {
        IntegerTerm::Machine(m) => {
            IntegerTerm::from_machine(m.ty(), native_term(m.value())).unwrap()
        }
        IntegerTerm::Add(a, b) => IntegerTerm::add(native_integer(a), native_integer(b)),
        IntegerTerm::Subtract(a, b) => IntegerTerm::subtract(native_integer(a), native_integer(b)),
        IntegerTerm::Multiply(a, b) => IntegerTerm::multiply(native_integer(a), native_integer(b)),
        value => value.clone(),
    }
}
fn native_domain(value: &Proposition) -> Proposition {
    let value = boxed_domain(value);
    match &value {
        Proposition::And(a, b) => {
            Proposition::And(Box::new(native_domain(a)), Box::new(native_domain(b)))
        }
        Proposition::Or(a, b) => {
            Proposition::Or(Box::new(native_domain(a)), Box::new(native_domain(b)))
        }
        Proposition::ConditionIs(c, t) => Proposition::ConditionIs(
            match c {
                ConditionTerm::IntegerEqual(a, b) => {
                    ConditionTerm::integer_equal(native_integer(a), native_integer(b))
                }
                ConditionTerm::IntegerLessEqual(a, b) => {
                    ConditionTerm::integer_less_equal(native_integer(a), native_integer(b))
                }
                ConditionTerm::IntegerGreaterEqual(a, b) => {
                    ConditionTerm::integer_greater_equal(native_integer(a), native_integer(b))
                }
                ConditionTerm::Compare {
                    format,
                    relation,
                    left,
                    right,
                } => ConditionTerm::Compare {
                    format: *format,
                    relation: *relation,
                    left: Box::new(native_term(left)),
                    right: Box::new(native_term(right)),
                },
                c => c.clone(),
            },
            *t,
        ),
        p => p.clone(),
    }
}

#[test]
fn common_call_observations_retain_roots_and_casts_match_native() {
    let _session = VerificationSession::enter();
    for source in FORMATS {
        let root = call(source, "observed_call");
        let exports = KernelTermExport::machine_export_count();
        let IntegerTerm::Machine(observed) =
            MachineOperandView::Shared(&root).observe(source).unwrap()
        else {
            panic!()
        };
        assert_eq!(observed.shared_operand(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        for destination in FORMATS
            .into_iter()
            .chain([MachineIntegerType::Int128, MachineIntegerType::UInt128])
        {
            super::super::super::signedness_cast_tests::check_native_parity(
                root.clone(),
                destination,
            );
        }
    }
}

#[test]
fn common_call_arithmetic_preserves_native_values_and_domains() {
    let _session = VerificationSession::enter();
    for a in FORMATS {
        for b in FORMATS {
            let l = call(a, "left_call");
            let r = call(b, "right_call");
            // The parity oracle needs fully materialized native inputs;
            // production handoffs intentionally retain argument handles.
            let native_l = a.value_from_term(KernelTermExport::machine(&l).unwrap());
            let native_r = b.value_from_term(KernelTermExport::machine(&r).unwrap());
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
            ] {
                for defined in [false, true] {
                    let mut execution = ExecutionBudget::new();
                    let mut budget = SpecEvaluation::logical(&mut execution);
                    budget.program_definedness = defined;
                    let expected = crate::kernel::eval::apply_spec_machine_arithmetic(
                        op,
                        if defined {
                            SpecDivision::CDefined
                        } else {
                            SpecDivision::Total
                        },
                        &native_l,
                        &native_r,
                        &ExecutionFacts::default(),
                        &[],
                    )
                    .unwrap();
                    let exports = KernelTermExport::machine_export_count();
                    let actual =
                        apply_values(Some(op), &l.clone().into(), &r.clone().into(), &budget)
                            .unwrap();
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    let ExpressionOutcome::Value(expected_value) = expected.outcome else {
                        panic!()
                    };
                    assert_eq!(
                        SpecValue::Shared(actual.value).into_native(),
                        expected_value,
                        "{a:?} {b:?} {op:?}"
                    );
                    let normalize = |debts: Vec<ProofObligation>| {
                        debts
                            .into_iter()
                            .map(|mut o| {
                                o.proposition = native_domain(o.proposition());
                                o
                            })
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(
                        normalize(actual.obligations),
                        normalize(expected.obligations),
                        "{a:?} {b:?} {op:?} defined{defined}"
                    );
                }
            }
        }
    }
}

#[test]
fn common_call_root_readings_keep_wide_refusals_and_borrow_arguments() {
    let _session = VerificationSession::enter();
    for format in FORMATS
        .into_iter()
        .chain([MachineIntegerType::Int128, MachineIntegerType::UInt128])
    {
        let root = call(format, "borrowed_call");
        let exports = KernelTermExport::machine_export_count();
        let leaf = root.machine_conversion_leaf().unwrap();
        let MachineTerm::ClickFunctionApplication { arguments, .. } = leaf else {
            panic!()
        };
        assert!(matches!(
            arguments[0],
            PureFunctionArgument::SharedMachine(_)
        ));
        assert!(std::ptr::eq(leaf, root.machine_conversion_leaf().unwrap()));
        assert_eq!(
            MachineOperandView::Shared(&root).root_width(),
            MachineOperandView::Legacy(leaf).root_width()
        );
        assert_eq!(
            MachineOperandView::Shared(&root).accepts_cast_operand(format),
            format.format().bits() != 128
        );
        assert_eq!(
            MachineOperandView::Shared(&root).observe(format).is_some(),
            format.format().bits() != 128
        );
        if format.format().bits() == 128 {
            assert!(cast(&root.clone().into(), ProgramType::Int32).is_none());
            let mut execution = ExecutionBudget::new();
            let budget = SpecEvaluation::logical(&mut execution);
            assert!(
                apply_values(
                    Some(MachineBinaryOp::Divide),
                    &root.clone().into(),
                    &root.clone().into(),
                    &budget
                )
                .is_none()
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_calls.rs");
}

#[test]
fn wide_call_identity_casts_keep_the_native_type_refusal() {
    let _session = VerificationSession::enter();
    for source in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        for target in [ProgramType::Int128, ProgramType::UInt128, ProgramType::Int32] {
            for count in [1, 3] {
                let root = call(source, "wide_call");
                let native = SpecValue::Shared(root.clone()).into_native();
                let state = ExecutionState::new();
                let mut values = crate::persistent::PersistentMap::default();
                values.insert("x".to_string(), root);
                for shared in [false, true] {
                    let mut expression = if shared {
                        SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()))
                    } else {
                        SpecExpression::Value(native.clone())
                    };
                    for _ in 0..count {
                        expression = SpecExpression::Cast(Box::new(expression), target);
                    }
                    let scope = SpecScope {
                        values: Some(&values),
                        ..SpecScope::unbound(&state, None)
                    };
                    let mut execution = ExecutionBudget::new();
                    let mut budget = SpecEvaluation::logical(&mut execution);
                    let exports = KernelTermExport::machine_export_count();
                    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                        scope,
                        &expression,
                        &PureFactContext::new(),
                        &mut budget,
                    )
                    .unwrap();
                    assert!(paths.is_empty());
                    assert_eq!(
                        budget.dropped_runtime_error,
                        Some(RuntimeError::TypeMismatch)
                    );
                    if shared {
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                    }
                }
            }
        }
    }
}

fn call_expression(format: MachineIntegerType, arguments: Vec<SpecExpression>) -> SpecExpression {
    SpecExpression::PureFunctionApplication {
        name: "produced_call".into(),
        arguments: arguments
            .into_iter()
            .map(SpecPureFunctionArgument::Value)
            .collect(),
        result_type: format.program_type(),
        pointer_result: None,
        result_object_class: None,
        projection: None,
    }
}

fn produced_paths(expression: &SpecExpression, legacy: bool) -> Vec<SpecExpressionPath> {
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    budget.machine_preparation_disabled = legacy;
    budget.machine_result_production_disabled = legacy;
    evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&ExecutionState::new(), None),
        expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap()
}

#[test]
fn actual_call_producers_keep_all_integer_types_and_nested_arguments() {
    let _session = VerificationSession::enter();
    let input = SpecExpression::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(995830))));
    for format in FORMATS
        .into_iter()
        .chain([MachineIntegerType::Int128, MachineIntegerType::UInt128])
    {
        for argument in [
            input.clone(),
            call_expression(MachineIntegerType::Int32, vec![input.clone()]),
        ] {
            let expression = call_expression(format, vec![argument]);
            let exports = KernelTermExport::machine_export_count();
            let paths = produced_paths(&expression, false);
            assert_eq!(paths.len(), 1);
            let SpecValue::Shared(root) = &paths[0].value else {
                panic!("common call result")
            };
            assert_eq!(root.ty(), &KernelType::Program(format.program_type()));
            assert!(matches!(root.node(), KernelTermNode::Call { .. }));
            assert!(paths[0].facts.is_empty());
            assert!(paths[0].obligations.is_empty());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let expected = produced_paths(&expression, true);
            let native = expected[0].value.clone().into_native();
            assert_eq!(
                KernelTermExport::machine(root).unwrap(),
                native_term(&program_value_bitvector_term(&native).unwrap())
            );
        }
    }
}

#[test]
fn actual_call_results_keep_deferred_bindings_and_wide_cast_refusals() {
    let _session = VerificationSession::enter();
    for format in FORMATS
        .into_iter()
        .chain([MachineIntegerType::Int128, MachineIntegerType::UInt128])
    {
        let call = call_expression(format, vec![]);
        let bound = SpecExpression::Let {
            name: "result".into(),
            value: Box::new(call.clone()),
            body: Box::new(SpecExpression::ProgramExpression(ProgramExpression::Variable(
                "result".into(),
            ))),
        };
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(produced_paths(&bound, false), produced_paths(&call, false));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if format.format().bits() == 128 {
            for target in [ProgramType::Int128, ProgramType::UInt128, ProgramType::Int32] {
                let cast = SpecExpression::Cast(Box::new(call.clone()), target);
                for legacy in [false, true] {
                    let mut execution = ExecutionBudget::new();
                    let mut budget = SpecEvaluation::logical(&mut execution);
                    budget.machine_result_production_disabled = legacy;
                    let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
                        SpecScope::unbound(&ExecutionState::new(), None),
                        &cast,
                        &PureFactContext::new(),
                        &mut budget,
                    )
                    .unwrap();
                    assert!(paths.is_empty());
                    assert_eq!(
                        budget.dropped_runtime_error,
                        Some(RuntimeError::TypeMismatch)
                    );
                }
            }
        }
    }
}

#[test]
fn actual_call_native_handoff_retains_nested_call_arguments() {
    let _session = VerificationSession::enter();
    let expression = call_expression(
        MachineIntegerType::Int32,
        vec![call_expression(MachineIntegerType::Int32, vec![])],
    );
    let mut paths = produced_paths(&expression, false);
    let SpecValue::Shared(root) = &paths[0].value else {
        panic!()
    };
    let child = root.children()[0].clone();
    let exports = KernelTermExport::machine_export_count();
    let native = paths.pop().unwrap().value.into_native();
    let ProgramValue::Int32(MachineTerm::ClickFunctionApplication { arguments, .. }) = native else {
        panic!()
    };
    let [PureFunctionArgument::SharedMachine(value)] = arguments.as_slice() else {
        panic!("handoff materialized the argument")
    };
    assert_eq!(value.shared_operand(), Some(&child));
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn actual_call_arithmetic_keeps_native_values_and_definedness() {
    let _session = VerificationSession::enter();
    let call = call_expression(MachineIntegerType::Int32, vec![]);
    let one = SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(1)));
    for expression in [
        SpecExpression::Add(Box::new(call.clone()), Box::new(one.clone())),
        SpecExpression::Divide(Box::new(one.clone()), Box::new(call.clone())),
        SpecExpression::Cast(Box::new(call.clone()), ProgramType::UInt64),
        call_expression(
            MachineIntegerType::Int32,
            vec![SpecExpression::Add(Box::new(call), Box::new(one))],
        ),
    ] {
        for defined in [false, true] {
            let evaluate = |legacy| {
                let mut execution = ExecutionBudget::new();
                let mut budget = SpecEvaluation::logical(&mut execution);
                budget.machine_preparation_disabled = legacy;
                budget.machine_result_production_disabled = legacy;
                budget.program_definedness = defined;
                evaluate_spec_expression_paths_with_algebraic_bindings_in(
                    SpecScope::unbound(&ExecutionState::new(), None),
                    &expression,
                    &PureFactContext::new(),
                    &mut budget,
                )
                .unwrap()
            };
            let exports = KernelTermExport::machine_export_count();
            let actual = evaluate(false);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let expected = evaluate(true);
            assert_eq!(actual.len(), expected.len());
            assert_eq!(actual.len(), 1);
            let SpecValue::Shared(root) = &actual[0].value else {
                panic!("retained result")
            };
            let native = expected[0].value.clone().into_native();
            assert_eq!(
                KernelTermExport::machine(root).unwrap(),
                program_value_bitvector_term(&native).unwrap()
            );
            assert_eq!(actual[0].facts, expected[0].facts);
            assert_eq!(actual[0].obligations.len(), expected[0].obligations.len());
            for (actual, expected) in actual[0].obligations.iter().zip(&expected[0].obligations) {
                assert_eq!(
                    native_domain(&actual.proposition),
                    native_domain(&expected.proposition)
                );
                assert_eq!(actual.evaluation_domain, expected.evaluation_domain);
                assert_eq!(actual.assumable, expected.assumable);
            }
        }
    }
}

#[test]
fn actual_call_comparisons_preserve_native_fact_forms() {
    let _session = VerificationSession::enter();
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let expression = call_expression(format, vec![]);
        let actual = produced_paths(&expression, false).pop().unwrap().value;
        let expected = produced_paths(&expression, true).pop().unwrap().value;
        let other =
            SpecValue::Native(format.value_from_term(MachineTerm::Variable(Variable(995832))));
        for op in [
            ComparisonOperator::Equal,
            ComparisonOperator::NotEqual,
            ComparisonOperator::LessThan,
            ComparisonOperator::LessEqual,
            ComparisonOperator::GreaterThan,
            ComparisonOperator::GreaterEqual,
        ] {
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                actual.comparison(op, &other).unwrap(),
                expected.comparison(op, &other).unwrap()
            );
            assert_eq!(
                other.comparison(op, &actual).unwrap(),
                other.comparison(op, &expected).unwrap()
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}
