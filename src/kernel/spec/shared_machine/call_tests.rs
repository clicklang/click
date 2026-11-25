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
            OldMachineTerm::Variable(Variable(995810)),
        ))],
    );
    KernelTermImport::default().machine_call(format, &application)
}
// Oracle-only materialization: argument carrier choice is not a change to
// the call's typed value. Production readers keep these handles retained.
fn native_term(value: &OldMachineTerm) -> OldMachineTerm {
    match value {
        OldMachineTerm::ClickFunctionApplication { name, arguments } => {
            OldMachineTerm::ClickFunctionApplication {
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
        OldMachineTerm::Cast {
            spelling,
            from,
            to,
            value,
        } => OldMachineTerm::Cast {
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
        Proposition::ConditionIs(c, t) => Proposition::condition_is(
            match c.old_form() {
                OldConditionTerm::IntegerEqual(a, b) => {
                    OldConditionTerm::integer_equal(native_integer(a), native_integer(b))
                }
                OldConditionTerm::IntegerLessEqual(a, b) => {
                    OldConditionTerm::integer_less_equal(native_integer(a), native_integer(b))
                }
                OldConditionTerm::IntegerGreaterEqual(a, b) => {
                    OldConditionTerm::integer_greater_equal(native_integer(a), native_integer(b))
                }
                OldConditionTerm::Compare {
                    format,
                    relation,
                    left,
                    right,
                } => OldConditionTerm::Compare {
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
        let OldMachineTerm::ClickFunctionApplication { arguments, .. } = leaf else {
            panic!()
        };
        assert!(matches!(
            arguments[0],
            PureFunctionArgument::SharedMachine(_)
        ));
        assert!(std::ptr::eq(leaf, root.machine_conversion_leaf().unwrap()));
        assert_eq!(
            MachineOperandView::Shared(&root).root_width(),
            MachineOperandView::Old(leaf).root_width()
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
        for target in [
            ProgramType::Int128,
            ProgramType::UInt128,
            ProgramType::Int32,
        ] {
            for count in [1, 3] {
                let root = call(source, "wide_call");
                let native = SpecValue::Shared(root.clone()).into_native();
                let state = ExecutionState::new();
                let mut values: crate::persistent::PersistentMap<
                    crate::kernel::BindingName,
                    crate::kernel::KernelTerm,
                > = crate::persistent::PersistentMap::default();
                values.insert("x".into(), root);
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
    let input = SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(995830))));
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
            body: Box::new(SpecExpression::ProgramExpression(
                ProgramExpression::Variable("result".into()),
            )),
        };
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(produced_paths(&bound, false), produced_paths(&call, false));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        if format.format().bits() == 128 {
            for target in [
                ProgramType::Int128,
                ProgramType::UInt128,
                ProgramType::Int32,
            ] {
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
    let ProgramValue::Int32(OldMachineTerm::ClickFunctionApplication { arguments, .. }) = native
    else {
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
    let one = SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(1)));
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
            SpecValue::Native(format.value_from_term(OldMachineTerm::Variable(Variable(995832))));
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

#[test]
fn pointer_call_producers_retain_nested_arguments_and_native_metadata() {
    let _session = VerificationSession::enter();
    let class = crate::kernel::effective_type::CAccessClass::Scalar(
        crate::kernel::effective_type::CScalarClass::Int,
    );
    for (null, mode) in [false, true]
        .into_iter()
        .flat_map(|null| (0..3).map(move |mode| (null, mode)))
    {
        let pointer = OldPointer::new(
            if null {
                Address::null()
            } else {
                Address::symbolic(Variable(1025100))
            },
            ProgramType::Int32Pointer,
        )
        .with_object_class(Some(class.clone()));
        let call = |argument| SpecExpression::PureFunctionApplication {
            name: "pointer_select".into(),
            arguments: vec![{
                let argument = if mode == 0 {
                    SpecPureFunctionArgument::Value(argument)
                } else {
                    SpecPureFunctionArgument::ArrayRef {
                        point: SpecPoint::Current,
                        pointer: argument,
                        element_type: ProgramType::Int32,
                    }
                };
                if mode == 2 {
                    SpecPureFunctionArgument::ObjectPointer {
                        argument: Box::new(argument),
                        object_class: class.clone(),
                    }
                } else {
                    argument
                }
            }],
            result_type: ProgramType::Int32Pointer,
            pointer_result: Some(std::sync::Arc::new(PurePointerResult {
                classes: BTreeSet::new(),
                arguments: BTreeSet::from([0]),
            })),
            result_object_class: Some(class.clone()),
        };
        let expression = call(call(SpecExpression::Value(ProgramValue::Pointer(pointer))));
        let retained = produced_paths(&expression, false);
        let native = produced_paths(&expression, true);
        assert_eq!(retained.len(), 1, "mode={mode} null={null}");
        assert_eq!(retained.len(), native.len());
        for (actual, expected) in retained.iter().zip(&native) {
            assert_eq!(
                actual.value.clone().into_native(),
                expected.value.clone().into_native()
            );
            assert_eq!(actual.facts, expected.facts);
            assert_eq!(actual.obligations, expected.obligations);
            let actual_pointer = actual.value.pointer().unwrap();
            let expected_pointer = expected.value.pointer().unwrap();
            assert_eq!(
                actual_pointer.object_class(),
                expected_pointer.object_class()
            );
            assert_eq!(
                actual_pointer.object_origin_evidence(),
                expected_pointer.object_origin_evidence()
            );
            if !null {
                let KernelTermNode::PointerCall { call, .. } =
                    actual.value.shared().unwrap().node()
                else {
                    panic!("retained pointer call");
                };
                let KernelTermNode::Call { arguments, .. } = call.node() else {
                    panic!("generic call")
                };
                let child = match arguments[0].node() {
                    KernelTermNode::ArrayReference { pointer, .. } => pointer,
                    _ => &arguments[0],
                };
                assert!(matches!(child.node(), KernelTermNode::PointerCall { .. }));
            }
        }
    }
}

#[test]
fn actual_boolean_call_results_retain_roots_and_native_handoff_behavior() {
    let _session = VerificationSession::enter();
    let call = |arguments| SpecExpression::PureFunctionApplication {
        name: "produced_boolean_call".into(),
        arguments,
        result_type: ProgramType::Bool,
        pointer_result: None,
        result_object_class: None,
    };
    let expression = call(vec![SpecPureFunctionArgument::Value(call_expression(
        MachineIntegerType::Int32,
        vec![],
    ))]);
    let paths = produced_paths(&expression, false);
    let root = paths[0].value.shared().expect("retained Boolean call");
    assert_eq!(root.ty(), &KernelType::Bool);
    assert_eq!(paths[0].value.program_type(), ProgramType::Bool);
    let native = paths[0].value.clone().into_native();
    assert_eq!(
        native,
        produced_paths(&expression, true)[0]
            .value
            .clone()
            .into_native()
    );
    for expression in [
        call(vec![SpecPureFunctionArgument::Value(expression.clone())]),
        SpecExpression::Let {
            name: "boolean_result".into(),
            value: Box::new(expression.clone()),
            body: Box::new(SpecExpression::ProgramExpression(
                ProgramExpression::Variable("boolean_result".into()),
            )),
        },
        SpecExpression::Cast(Box::new(expression), ProgramType::Bool),
    ] {
        assert_eq!(
            native_results(produced_paths(&expression, false)),
            native_results(produced_paths(&expression, true))
        );
    }
}

#[test]
fn boolean_call_handoffs_retain_nested_boolean_arguments() {
    let _session = VerificationSession::enter();
    let call = |arguments| SpecExpression::PureFunctionApplication {
        name: "boolean_handoff".into(),
        arguments,
        result_type: ProgramType::Bool,
        pointer_result: None,
        result_object_class: None,
    };
    let inner = call(vec![]);
    let inner_paths = produced_paths(&inner, false);
    let expected = inner_paths[0].value.shared().unwrap().clone();
    let expression = SpecExpression::Let {
        name: "b".into(),
        value: Box::new(inner),
        body: Box::new(call(vec![SpecPureFunctionArgument::Value(
            SpecExpression::ProgramExpression(ProgramExpression::Variable("b".into())),
        )])),
    };
    let paths = produced_paths(&expression, false);
    let root = paths[0].value.shared().unwrap();
    let KernelTermNode::Call { arguments, .. } = root.node() else {
        panic!()
    };
    assert_eq!(arguments, &[expected]);
    assert_eq!(
        native_results(paths),
        native_results(produced_paths(&expression, true))
    );
}

#[test]
fn boolean_composition_producers_preserve_casts_and_comparison_rules() {
    let _session = VerificationSession::enter();
    let condition = OldConditionTerm::Variable(Variable(999440));
    let native = ProgramValue::Bool(OldMachineTerm::bool_cast(
        MachineIntegerType::UInt8,
        condition.clone(),
    ));
    let left = SpecValue::Shared(KernelTermImport::default().condition(&condition));
    let right_condition = OldConditionTerm::Variable(Variable(999441));
    let right = SpecValue::Shared(KernelTermImport::default().condition(&right_condition));
    let guard = Proposition::condition_is(OldConditionTerm::Variable(Variable(999442)), false);
    let combined = SpecValue::conditional(&guard, &left, &right, true)
        .unwrap()
        .unwrap();
    assert!(matches!(
        combined.shared().unwrap().node(),
        KernelTermNode::BoolIf { .. }
    ));
    assert_eq!(
        combined.clone().into_native(),
        conditional_spec_value(
            &guard,
            left.clone().into_native(),
            right.clone().into_native()
        )
        .unwrap()
    );
    for target in FORMATS
        .into_iter()
        .chain([MachineIntegerType::Int128, MachineIntegerType::UInt128])
    {
        let cast = cast(&combined, target.program_type()).unwrap();
        assert!(matches!(cast.node(), KernelTermNode::BoolCast { .. }));
        let expression = SpecExpression::Cast(
            Box::new(SpecExpression::Value(native.clone())),
            target.program_type(),
        );
        assert_eq!(
            native_results(produced_paths(&expression, false)),
            native_results(produced_paths(&expression, true))
        );
    }
    for right in [
        right,
        SpecValue::Native(ProgramValue::Bool(OldMachineTerm::Variable(Variable(999443)))),
        SpecValue::Native(ProgramValue::Bool(OldMachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            OldConditionTerm::Constant(true),
        ))),
        SpecValue::Shared(KernelTermImport::default().condition(&OldConditionTerm::Constant(false))),
        SpecValue::Native(ProgramValue::Int32(OldMachineTerm::constant(1))),
    ] {
        for op in [
            ComparisonOperator::Equal,
            ComparisonOperator::NotEqual,
            ComparisonOperator::LessThan,
        ] {
            assert_eq!(
                left.comparison(op, &right),
                SpecValue::Native(left.clone().into_native())
                    .comparison(op, &SpecValue::Native(right.clone().into_native()))
            );
        }
    }
}

#[test]
fn cold_native_array_argument_retains_the_entry_point_across_local_stores() {
    let _session = VerificationSession::enter();
    let local = Address {
        base: "local:unrelated".into(),
        offset: OldAddressOffset::Constant(0),
    };
    let pointer = Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0),
    };
    let argument = SpecPureFunctionArgument::ArrayRef {
        point: SpecPoint::Current,
        pointer: SpecExpression::Value(ProgramValue::typed_pointer(
            pointer,
            ProgramType::Int32Pointer,
        )),
        element_type: ProgramType::Int32,
    };
    let entry = ExecutionState::new().begin_function_entry_memory();
    let read = |state: &ExecutionState| {
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_result_production_disabled = true;
        let paths = evaluate_spec_pure_function_argument_paths_in(
            SpecScope::unbound(state, None),
            &argument,
            &PureFactContext::new(),
            &mut budget,
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one argument path");
        };
        let SpecCallArgument::Native(PureFunctionArgument::ArrayRef { point, .. }) = &path.value
        else {
            panic!("native array argument");
        };
        assert_eq!(point.read_version_id(), entry.observation_point_id());
        let SpecCallArgument::Native(argument) = &path.value else {
            unreachable!()
        };
        let root = KernelTermImport::default().argument(argument);
        assert_eq!(
            KernelTermExport::default().argument(&root).unwrap(),
            *argument
        );
        argument.clone()
    };
    let work = [4, 16, 64].map(|count| {
        let mut state = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(local.base.clone(), 4));
        for value in 0..count {
            state = state
                .clone()
                .with_memory(state.memory().clone().store(local.clone(), int32(value)));
        }
        let (argument, work) = crate::instrumentation::measure_deterministic_work(|| read(&state));
        assert_eq!(argument, read(&entry));
        work
    });
    assert!(work.iter().all(|cost| *cost <= work[0] + 5), "{work:?}");
}

#[test]
fn external_array_entry_crosses_checked_local_calls_with_bounded_cold_work() {
    let _session = VerificationSession::enter();
    let array = Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0),
    };
    let local = Address {
        base: "local:callee-write".into(),
        offset: OldAddressOffset::Constant(0),
    };
    let other = Address {
        base: "local:other-callee-write".into(),
        offset: OldAddressOffset::Constant(0),
    };
    let argument = ProgramValue::typed_pointer(array.clone(), ProgramType::Int32Pointer);
    let entry = ExecutionState::new().begin_function_entry_memory();
    let expected = array_ref_argument_point(&entry.program_point(), &argument);
    assert_eq!(expected.read_version_id(), entry.observation_point_id());
    let declared = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(local.base.clone(), 4)
            .with_block(other.base.clone(), 4),
    );
    let assumptions = PureFactContext::new();
    let call = |state: &ExecutionState, changed: &Address, index| {
        state.memory().clone().with_call_memory_havoc(
            Variable(index),
            &[
                MemoryRange::new(local.clone(), 0.into(), 1.into()),
                MemoryRange::new(changed.clone(), 0.into(), 1.into()),
            ],
            &assumptions,
            None,
        )
    };
    let work = [1, 8, 64].map(|count| {
        let mut state = declared.clone();
        for index in 0..count {
            let effects = call(&state, &other, 1011300 + index).store(local.clone(), int32(2));
            state = state.with_memory(effects);
        }
        let current = state.program_point();
        assert!(
            current
                .entry_integer_version(&array, LoadKind::Int32)
                .is_none()
        );
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            array_ref_argument_point(&current, &argument)
        });
        assert_eq!(selected, expected);
        work
    });
    assert!(work.iter().all(|units| *units == work[0]), "{work:?}");

    let can_write = declared
        .clone()
        .with_memory(call(&declared, &array, 1011400));
    let wrote = declared
        .clone()
        .with_memory(declared.memory().clone().store(array, int32(9)));
    let symbolic = declared.clone().with_memory(call(
        &declared,
        &Address::symbolic(Variable(1011401)),
        1011402,
    ));
    for changed in [can_write, symbolic] {
        let point = changed.program_point();
        assert!(
            point
                .indexed_array_version(&AddressBase::ExternalArgument)
                .is_none()
        );
        assert_ne!(array_ref_argument_point(&point, &argument), expected);
        let later = changed.clone().with_memory(call(&changed, &other, 1011403));
        assert!(
            later
                .program_point()
                .indexed_array_version(&AddressBase::ExternalArgument)
                .is_none()
        );
    }

    let after_write = array_ref_argument_point(&wrote.program_point(), &argument);
    assert_eq!(after_write.read_version_id(), wrote.observation_point_id());
    assert_ne!(after_write, expected);
    let work = [1, 8, 64, 256].map(|count| {
        let mut state = wrote.clone();
        for index in 0..count {
            let effects = call(&state, &other, 1011500 + index).store(local.clone(), int32(3));
            state = state.with_memory(effects);
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            array_ref_argument_point(&state.program_point(), &argument)
        });
        assert_eq!(selected, after_write);
        work
    });
    assert!(work.iter().all(|units| *units == work[0]), "{work:?}");
}

#[test]
fn static_array_versions_select_their_own_write_across_disjoint_calls() {
    let _session = VerificationSession::enter();
    let g = SymbolicMemory::global_pointer("g");
    let h = SymbolicMemory::global_pointer("h");
    let pointer = |address| ProgramValue::typed_pointer(address, ProgramType::Int32Pointer);
    let g_argument = pointer(g.clone());
    let h_argument = pointer(h.clone());
    let entry = ExecutionState::new()
        .with_memory(
            SymbolicMemory::new()
                .with_block(g.base.clone(), 4)
                .with_block(h.base.clone(), 4),
        )
        .begin_function_entry_memory();
    let version =
        |state: &ExecutionState, pointer| array_ref_argument_point(&state.program_point(), pointer);
    let entry_h = version(&entry, &h_argument);
    assert_eq!(entry_h.read_version_id(), entry.observation_point_id());
    let written = entry
        .clone()
        .with_memory(entry.memory().clone().store(h.clone(), int32(7)));
    let written_h = version(&written, &h_argument);
    assert_eq!(written_h.read_version_id(), written.observation_point_id());
    assert_ne!(written_h, entry_h);
    assert_eq!(version(&written, &g_argument), version(&entry, &g_argument));

    let assumptions = PureFactContext::new();
    let call = |state: &ExecutionState, address: &Address, id| {
        state
            .clone()
            .with_memory(state.memory().clone().with_call_memory_havoc(
                Variable(id),
                &[MemoryRange::new(address.clone(), 0.into(), 1.into())],
                &assumptions,
                None,
            ))
    };
    let work = [1, 8, 64, 256].map(|count| {
        let mut state = written.clone();
        for index in 0..count {
            state = call(&state, &g, 1013000 + index);
        }
        let (selected, work) =
            crate::instrumentation::measure_deterministic_work(|| version(&state, &h_argument));
        assert_eq!(selected, written_h);
        assert_eq!(
            version(&state, &g_argument).read_version_id(),
            state.observation_point_id()
        );
        work
    });
    assert!(work.iter().all(|units| *units <= work[0] + 4), "{work:?}");

    let unknown = call(&written, &Address::symbolic(Variable(1013500)), 1013501);
    assert!(
        unknown
            .program_point()
            .indexed_array_version(&h.base)
            .is_none()
    );
}

#[test]
fn heap_array_versions_ignore_disjoint_local_stores() {
    let _session = VerificationSession::enter();
    let other = SymbolicMemory::local_pointer("unrelated");
    let request = Address::symbolic(Variable(1013830));
    let entry = ExecutionState::new().begin_function_entry_memory();
    let pending = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(other.base.clone(), 4)
            .with_pending_heap_allocation(
                request.clone(),
                crate::kernel::AllocationSize::int32(4),
                false,
            ),
    );
    let (memory, _, array) = pending
        .memory()
        .clone()
        .resolve_pending_heap_allocation(&request, true)
        .expect("successful allocation");
    let allocated = pending.with_memory(memory);
    let written = allocated
        .clone()
        .with_memory(allocated.memory().clone().store(array.clone(), int32(7)));
    let argument = ProgramValue::typed_pointer(array.clone(), ProgramType::Int32Pointer);
    let expected = written.observation_point_id();
    let samples = [1, 8, 64, 256].map(|count| {
        let mut state = written.clone();
        for index in 0..count {
            let memory = state.memory().clone().store(other.clone(), int32(index));
            state = state.with_memory(memory);
        }
        crate::kernel::resource_tracker::clear_version_memos();
        let point = state.program_point();
        let (version, work) = crate::instrumentation::measure_deterministic_work(|| {
            array_ref_argument_point(&point, &argument)
        });
        (version.read_version_id(), work)
    });
    let work = samples.map(|(_, work)| work);
    assert!(work.iter().all(|units| *units <= work[0] + 4), "{work:?}");
    assert!(
        samples.iter().all(|(version, _)| *version == expected),
        "{samples:?}"
    );

    let rewritten = written
        .clone()
        .with_memory(written.memory().clone().store(array.clone(), int32(7)));
    assert_eq!(
        array_ref_argument_point(&rewritten.program_point(), &argument).read_version_id(),
        rewritten.observation_point_id(),
    );
    assert_ne!(rewritten.observation_point_id(), expected);
    let memory = rewritten
        .memory()
        .clone()
        .free_heap_block(&array, &PureFactContext::new())
        .expect("free the live allocation");
    let freed = rewritten.with_memory(memory);
    assert!(
        freed
            .program_point()
            .indexed_array_version(&array.base)
            .is_none()
    );
}

#[test]
fn automatic_array_versions_select_writes_across_disjoint_local_effects() {
    let _session = VerificationSession::enter();
    let array = SymbolicMemory::local_pointer("array");
    let other = SymbolicMemory::local_pointer("other");
    let argument = ProgramValue::typed_pointer(array.clone(), ProgramType::Int32Pointer);
    let entry = ExecutionState::new().begin_function_entry_memory();
    let declared = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .with_block(array.base.clone(), 4)
            .with_block(other.base.clone(), 4),
    );
    let assumptions = PureFactContext::new();
    let call = |state: &ExecutionState, address: &Address, id| {
        state
            .clone()
            .with_memory(state.memory().clone().with_call_memory_havoc(
                Variable(id),
                &[MemoryRange::new(address.clone(), 0.into(), 1.into())],
                &assumptions,
                None,
            ))
    };
    let version =
        |state: &ExecutionState| array_ref_argument_point(&state.program_point(), &argument);
    let write = |state: &ExecutionState| {
        state
            .clone()
            .with_memory(state.memory().clone().store(array.clone(), int32(7)))
    };
    let unknown = call(&declared, &Address::symbolic(Variable(1013600)), 1013601);
    assert!(
        unknown
            .program_point()
            .indexed_array_version(&array.base)
            .is_none()
    );

    let first = write(&unknown);
    let expected = version(&first);
    assert_eq!(expected.read_version_id(), first.observation_point_id());
    let second = write(&first);
    assert_eq!(first.memory(), second.memory());
    assert_ne!(expected, version(&second));
    let ended = second.clone().with_memory(
        second
            .memory()
            .clone()
            .store(array.clone(), int32(8))
            .without_local_block(&array.base),
    );
    assert!(
        ended
            .program_point()
            .indexed_array_version(&array.base)
            .is_none()
    );

    let work = [1, 8, 64, 256].map(|count| {
        let mut state = first.clone();
        for index in 0..count {
            state = call(&state, &other, 1013700 + index);
        }
        let (observed, work) =
            crate::instrumentation::measure_deterministic_work(|| version(&state));
        assert_eq!(observed, expected);
        work
    });
    assert!(work.iter().all(|units| *units <= work[0] + 4), "{work:?}");
}

#[test]
fn pure_function_array_keeps_its_selected_point_without_an_indexed_version() {
    let _session = VerificationSession::enter();
    let array = Address::symbolic(Variable(1013811));
    let argument = SpecPureFunctionArgument::ArrayRef {
        point: SpecPoint::Current,
        pointer: SpecExpression::Value(ProgramValue::typed_pointer(
            array.clone(),
            ProgramType::Int32Pointer,
        )),
        element_type: ProgramType::Int32,
    };
    let first = ExecutionState::new().begin_function_entry_memory();
    let second = ExecutionState::new().begin_function_entry_memory();
    assert_eq!(first.memory(), second.memory());

    for state in [&first, &second] {
        assert!(
            state
                .program_point()
                .indexed_array_version(&array.base)
                .is_none()
        );
        for native in [false, true] {
            let mut execution = ExecutionBudget::new();
            let mut budget = SpecEvaluation::logical(&mut execution);
            budget.machine_result_production_disabled = native;
            let paths = evaluate_spec_pure_function_argument_paths_in(
                SpecScope::unbound(state, None),
                &argument,
                &PureFactContext::new(),
                &mut budget,
            )
            .unwrap();
            let [path] = paths.as_slice() else {
                panic!("one array argument path");
            };
            let argument = match &path.value {
                SpecCallArgument::Native(argument) => argument.clone(),
                SpecCallArgument::Shared(root) => {
                    KernelTermExport::default().argument(root).unwrap()
                }
            };
            let PureFunctionArgument::ArrayRef { point, .. } = argument else {
                panic!("array argument retains a point");
            };
            assert_eq!(point.read_version_id(), state.observation_point_id());
        }
    }
}

#[test]
fn declared_predicate_array_keeps_its_selected_point_without_an_indexed_version() {
    let _session = VerificationSession::enter();
    let array = Address::symbolic(Variable(1013810));
    let arguments = [SpecPredicateArgument::ArrayRef {
        point: SpecPoint::Current,
        pointer: SpecExpression::Value(ProgramValue::typed_pointer(
            array.clone(),
            ProgramType::Int32Pointer,
        )),
    }];
    let first = ExecutionState::new().begin_function_entry_memory();
    let second = ExecutionState::new().begin_function_entry_memory();
    assert_eq!(first.memory(), second.memory());

    for state in [&first, &second] {
        assert!(
            state
                .program_point()
                .indexed_array_version(&array.base)
                .is_none()
        );
        let mut execution = ExecutionBudget::new();
        let paths = lower_spec_predicate_proposition_at_state_in(
            SpecScope::unbound(state, None),
            "array_predicate",
            &arguments,
            false,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one predicate path");
        };
        let Proposition::Predicate { arguments, .. } = &path.proposition else {
            panic!("declared predicate");
        };
        let [_, Term::ArrayReadPoint(point), Term::ProgramValue(_)] = arguments.as_slice() else {
            panic!("array argument retains a point");
        };
        assert_eq!(point.read_version_id(), state.observation_point_id());
    }
}

#[test]
fn declared_predicate_array_names_its_entry_point_after_local_calls() {
    let _session = VerificationSession::enter();
    let array = Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(0),
    };
    let local = Address {
        base: "local:callee-write".into(),
        offset: OldAddressOffset::Constant(0),
    };
    let arguments = [SpecPredicateArgument::ArrayRef {
        point: SpecPoint::Current,
        pointer: SpecExpression::Value(ProgramValue::typed_pointer(
            array.clone(),
            ProgramType::Int32Pointer,
        )),
    }];
    let assumptions = PureFactContext::new();
    let lower = |state: &ExecutionState| {
        let mut execution = ExecutionBudget::new();
        let paths = lower_spec_predicate_proposition_at_state_in(
            SpecScope::unbound(state, None),
            "array_predicate",
            &arguments,
            false,
            &assumptions,
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one predicate path");
        };
        path.proposition.clone()
    };
    let entry = ExecutionState::new().begin_function_entry_memory();
    let expected = lower(&entry);
    let Proposition::Predicate { arguments, .. } = &expected else {
        panic!("declared predicate");
    };
    let [_, Term::ArrayReadPoint(point), Term::ProgramValue(_)] = arguments.as_slice() else {
        panic!("array argument retains a point");
    };
    assert_eq!(point.read_version_id(), entry.observation_point_id());
    let independent = ExecutionState::new().begin_function_entry_memory();
    assert_eq!(entry.memory(), independent.memory());
    assert_ne!(expected, lower(&independent));

    let call = |state: &ExecutionState, changed: &Address, index| {
        state
            .clone()
            .with_memory(state.memory().clone().with_call_memory_havoc(
                Variable(index),
                &[MemoryRange::new(changed.clone(), 0.into(), 1.into())],
                &assumptions,
                None,
            ))
    };
    let work = [1, 8, 64].map(|count| {
        let mut state = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(local.base.clone(), 4));
        for index in 0..count {
            state = call(&state, &local, 1011700 + index);
        }
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| lower(&state));
        assert_eq!(lowered, expected);
        work
    });
    assert!(work.iter().all(|units| *units == work[0]), "{work:?}");
    assert_ne!(lower(&call(&entry, &array, 1011800)), expected);
}
