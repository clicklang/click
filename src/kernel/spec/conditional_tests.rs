use super::*;
use crate::kernel::VerificationSession;

fn word(format: MachineIntegerType, value: i64) -> SpecValue {
    SpecValue::Shared(KernelTerm::retained_native_machine_operand(
        format,
        &crate::kernel::machine_integer::range::constant_word(format, &value.into()).unwrap(),
    ))
}
fn variable(format: MachineIntegerType, id: u64) -> SpecValue {
    SpecValue::Shared(KernelTerm::variable(
        KernelType::Program(format.program_type()),
        Variable(id),
    ))
}
fn join(condition: &ConditionTerm, left: &SpecValue, right: &SpecValue) -> SpecValue {
    SpecValue::conditional(
        &Proposition::condition_is(condition.clone(), true),
        left,
        right,
        true,
    )
    .unwrap()
    .unwrap()
}

#[test]
fn conditional_arms_keep_shared_identity_and_native_observations() {
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let _session = VerificationSession::enter();
        let x = variable(format, 998100);
        let one = word(format, 1);
        let mut execution = ExecutionBudget::new();
        let left = SpecValue::Shared(
            shared_machine::apply_values(
                Some(MachineBinaryOp::Add),
                &x,
                &one,
                &SpecEvaluation::logical(&mut execution),
            )
            .unwrap()
            .value,
        );
        let right = variable(format, 998101);
        let guard = ConditionTerm::Variable(Variable(998102));
        let native = conditional_spec_value(
            &Proposition::condition_is(guard.clone(), true),
            left.clone().into_native(),
            right.clone().into_native(),
        )
        .unwrap();
        let exports = KernelTermExport::machine_export_count();
        let result = join(&guard, &left, &right);
        let SpecValue::Shared(root) = &result else {
            panic!("retained join")
        };
        let KernelTermNode::MachineIf { arguments } = root.node() else {
            panic!("conditional node")
        };
        let SpecValue::Shared(left) = left else {
            unreachable!()
        };
        assert_eq!(arguments[1], left);
        assert_eq!(result.observe(), SpecValue::Native(native).observe());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let repeated = join(&guard, &result, &result);
        let KernelTermNode::MachineIf { arguments } = repeated.shared().unwrap().node() else {
            panic!("conditional with equal arms")
        };
        assert_eq!(&arguments[1..], &[root.clone(), root.clone()]);
    }
}

#[test]
fn opaque_guard_observations_keep_identity_without_exporting_arms() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::UInt64;
    let guard = |id| {
        ConditionTerm::address_equal(
            Address::symbolic(Variable(id)),
            Address::symbolic(Variable(998110)),
        )
    };
    let left = variable(format, 998111);
    let right = word(format, 0);
    let exports = KernelTermExport::machine_export_count();
    let first = join(&guard(998112), &left, &right).observe();
    assert_eq!(first, join(&guard(998112), &left, &right).observe());
    assert_ne!(first, join(&guard(998113), &left, &right).observe());
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn conditional_join_preserves_mixed_word_rules_and_bool_refusals() {
    let _session = VerificationSession::enter();
    let left = variable(MachineIntegerType::Int32, 998120);
    let right = variable(MachineIntegerType::UInt32, 998121);
    let guard = ConditionTerm::Variable(Variable(998122));
    let result = join(&guard, &left, &right);
    assert_eq!(result.program_type(), ProgramType::UInt32);
    let expected = conditional_spec_value(
        &Proposition::condition_is(guard.clone(), true),
        left.clone().into_native(),
        right.clone().into_native(),
    )
    .unwrap();
    assert_eq!(result.into_native(), expected);
    let boolean = SpecValue::Native(ProgramValue::Bool(MachineTerm::bool_cast(
        MachineIntegerType::UInt8,
        guard.clone(),
    )));
    assert!(matches!(
        SpecValue::conditional(
            &Proposition::condition_is(guard, true),
            &boolean,
            &left,
            true
        ),
        Err(ExecutionLimit::MixedBoolArms)
    ));
}

#[test]
fn conditional_evaluation_keeps_guarded_domains_and_ignores_ambient_truth() {
    let _session = VerificationSession::enter();
    let state =
        ExecutionState::new().with_local("x", int32(MachineTerm::Variable(Variable(998130))));
    let x = || SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
    let condition = SpecProposition::Comparison {
        left: x(),
        operator: ComparisonOperator::GreaterThan,
        right: SpecExpression::Value(int32(0)),
    };
    let expression = SpecExpression::If {
        condition: Box::new(condition),
        then_branch: Box::new(SpecExpression::Add(
            Box::new(x()),
            Box::new(SpecExpression::Value(int32(1))),
        )),
        else_branch: Box::new(SpecExpression::Value(int32(0))),
    };
    let evaluate = |facts: &PureFactContext, disabled| {
        let mut execution = ExecutionBudget::new();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_result_production_disabled = disabled;
        evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&state, None),
            &expression,
            facts,
            &mut budget,
        )
        .unwrap()
        .remove(0)
    };
    let empty = PureFactContext::new();
    let native = evaluate(&empty, true);
    let retained = evaluate(&empty, false);
    assert_eq!(retained.value.observe(), native.value.observe());
    assert_eq!(retained.obligations, native.obligations);
    assert!(!retained.obligations.is_empty());
    let condition = ConditionTerm::machine_compare(
        MachineIntegerType::Int32,
        CompareRelation::GreaterThan,
        MachineTerm::Variable(Variable(998130)),
        MachineTerm::constant(0),
    );
    for truth in [false, true] {
        assert_eq!(
            retained.value,
            evaluate(
                &empty.clone().assume_condition(condition.clone(), truth),
                false
            )
            .value
        );
    }
}

mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/conditional_tests.rs");
}

#[test]
fn independent_opaque_call_guard_imports_have_the_same_observation() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let guard = ConditionTerm::equal(
        MachineTerm::ClickFunctionApplication {
            name: "flag".into(),
            arguments: vec![],
        },
        MachineTerm::constant(1),
    );
    let left = variable(format, 998204);
    let right = word(format, 0);
    let exports = KernelTermExport::machine_export_count();
    let first = join(&guard, &left, &right).observe();
    for _ in 0..8 {
        assert_eq!(first, join(&guard, &left, &right).observe());
    }
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn exact_rewrites_keep_opaque_conditional_observation_identity() {
    use crate::kernel::proof::term_rewrite::TermRewrite;
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let guard = ConditionTerm::address_equal(
        Address::symbolic(Variable(998205)),
        Address::symbolic(Variable(998206)),
    );
    let source = join(&guard, &word(format, 1), &word(format, 0))
        .observe()
        .unwrap();
    let from: SharedIntegerTerm = IntegerTerm::constant(99.into()).into();
    let to: SharedIntegerTerm = IntegerTerm::constant(100.into()).into();
    let mut current = source.clone();
    let exports = KernelTermExport::machine_export_count();
    for _ in 0..8 {
        current = TermRewrite::for_integer_exact(&from, &to).integer(&current);
        assert_eq!(current, source);
    }
    let goal = Proposition::condition_is(
        ConditionTerm::integer_less_equal(IntegerTerm::constant(1.into()), source),
        true,
    );
    let unrelated = Proposition::condition_is(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(998207)),
            MachineTerm::constant(99),
        ),
        true,
    );
    for _ in 0..8 {
        assert!(
            !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(&goal, &unrelated)
        );
    }
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn pointer_conditional_handoffs_keep_selected_roots_metadata_and_refusals() {
    let _session = VerificationSession::enter();
    let pointer = Pointer::new(
        Address::symbolic(Variable(1026100)),
        ProgramType::Int32Pointer,
    )
    .with_pointee_constant(true)
    .with_pointee_volatile(true);
    let native = SpecValue::Native(ProgramValue::Pointer(pointer.clone()));
    let shared = native.clone().retain_pointer_result();
    let other_payload = SpecValue::Native(ProgramValue::Pointer(
        pointer.clone().with_pointee_constant(false),
    ));
    let condition = Proposition::condition_is(ConditionTerm::Variable(Variable(1026101)), true);
    for left in [native.clone(), shared.clone()] {
        for right in [
            other_payload.clone(),
            other_payload.clone().retain_pointer_result(),
        ] {
            let result = SpecValue::conditional(&condition, &left, &right, true)
                .unwrap()
                .unwrap();
            assert!(result.shared().is_some());
            if let Some(root) = left.shared() {
                assert_eq!(result.shared(), Some(root));
            }
            assert_eq!(result.clone().into_native(), native.clone().into_native());
            assert!(result.pointer().unwrap().pointee_constant());
            assert!(result.pointer().unwrap().pointee_volatile());
        }
    }
    let distinct = SpecValue::Native(ProgramValue::Pointer(Pointer::new(
        Address::symbolic(Variable(1026102)),
        ProgramType::Int32Pointer,
    )));
    for retain in [false, true] {
        assert!(
            SpecValue::conditional(&condition, &shared, &distinct, retain)
                .unwrap()
                .is_none()
        );
    }
    for truth in [false, true] {
        let expression = SpecExpression::If {
            condition: Box::new(SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(int32(if truth { 0 } else { 1 })),
            }),
            then_branch: Box::new(SpecExpression::Value(native.clone().into_native())),
            else_branch: Box::new(SpecExpression::Value(distinct.clone().into_native())),
        };
        let mut execution = ExecutionBudget::new();
        let paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
            SpecScope::unbound(&ExecutionState::new(), None),
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert!(paths[0].value.shared().is_some());
        assert_eq!(
            paths[0].value.clone().into_native(),
            if truth {
                native.clone().into_native()
            } else {
                distinct.clone().into_native()
            }
        );
    }
}

fn closed_comparison_if(
    then_branch: SpecExpression,
    else_branch: SpecExpression,
    operator: ComparisonOperator,
    truth: bool,
) -> SpecExpression {
    let bound = match operator {
        ComparisonOperator::LessThan => {
            if truth {
                10
            } else {
                8
            }
        }
        ComparisonOperator::Equal => {
            if truth {
                9
            } else {
                8
            }
        }
        ComparisonOperator::NotEqual => {
            if truth {
                8
            } else {
                9
            }
        }
        _ => unreachable!("test guard operator"),
    };
    SpecExpression::If {
        condition: Box::new(SpecProposition::Comparison {
            left: SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(9))),
            operator,
            right: SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(bound))),
        }),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

fn closed_order_if(
    then_branch: SpecExpression,
    else_branch: SpecExpression,
    truth: bool,
) -> SpecExpression {
    closed_comparison_if(
        then_branch,
        else_branch,
        ComparisonOperator::LessThan,
        truth,
    )
}

fn lower_closed_order_if(
    expression: &SpecExpression,
    facts: &PureFactContext,
) -> SpecExpressionPath {
    let state = ExecutionState::new();
    let mut execution = ExecutionBudget::new();
    evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&state, None),
        expression,
        facts,
        &mut SpecEvaluation::logical(&mut execution),
    )
    .unwrap()
    .remove(0)
}

#[test]
fn closed_order_guard_stays_in_the_lowered_machine_value() {
    let _session = VerificationSession::enter();
    let value = |n| SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(n)));
    for truth in [true, false] {
        let path = lower_closed_order_if(
            &closed_order_if(value(9), value(3), truth),
            &PureFactContext::new(),
        );
        let SpecValue::Shared(root) = path.value else {
            panic!("a retained machine value")
        };
        let KernelTermNode::MachineIf { arguments } = root.node() else {
            panic!("conditional must remain")
        };
        assert!(matches!(
            arguments[0].node(),
            KernelTermNode::BoolCompare { .. }
        ));
        assert!(path.obligations.is_empty());
    }
}
