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
        KernelType::C(format.c_type()),
        Variable(id),
    ))
}
fn join(condition: &ConditionTerm, left: &SpecValue, right: &SpecValue) -> SpecValue {
    SpecValue::conditional(
        &Proposition::ConditionIs(condition.clone(), true),
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
            &Proposition::ConditionIs(guard.clone(), true),
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
        assert_eq!(join(&guard, &result, &result), result);
    }
}

#[test]
fn opaque_guard_observations_keep_identity_without_exporting_arms() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::UInt64;
    let guard = |id| {
        ConditionTerm::pointer_equal(
            Pointer::symbolic(Variable(id)),
            Pointer::symbolic(Variable(998110)),
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
    assert_eq!(result.c_type(), ProgramType::UInt32);
    let expected = conditional_spec_value(
        &Proposition::ConditionIs(guard.clone(), true),
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
            &Proposition::ConditionIs(guard, true),
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
        operator: CComparisonOperator::GreaterThan,
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
    let guard = ConditionTerm::pointer_equal(
        Pointer::symbolic(Variable(998205)),
        Pointer::symbolic(Variable(998206)),
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
    let goal = Proposition::ConditionIs(
        ConditionTerm::integer_less_equal(IntegerTerm::constant(1.into()), source),
        true,
    );
    let unrelated = Proposition::ConditionIs(
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
