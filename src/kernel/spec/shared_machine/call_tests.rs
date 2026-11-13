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
        vec![PureFunctionArgument::Value(CValue::Int32(
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
                                    MachineIntegerType::from_c_type(value.c_type())
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
            let native_l = SpecValue::Shared(l.clone()).into_native();
            let native_r = SpecValue::Shared(r.clone()).into_native();
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
                    budget.c_definedness = defined;
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
                    let CExpressionOutcome::Value(expected_value) = expected.outcome else {
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
            assert!(cast(&root.clone().into(), CType::Int32).is_none());
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
        for target in [CType::Int128, CType::UInt128, CType::Int32] {
            for count in [1, 3] {
                let root = call(source, "wide_call");
                let native = SpecValue::Shared(root.clone()).into_native();
                let state = CState::new();
                let mut values = crate::persistent::PersistentMap::default();
                values.insert("x".to_string(), root);
                for shared in [false, true] {
                    let mut expression = if shared {
                        SpecExpression::CExpression(CExpression::Variable("x".into()))
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
                        Some(CRuntimeError::TypeMismatch)
                    );
                    if shared {
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                    }
                }
            }
        }
    }
}
