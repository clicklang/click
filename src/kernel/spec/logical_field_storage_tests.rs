use super::*;
use crate::kernel::VerificationSession;

#[test]
fn logical_resource_field_projections_keep_stored_roots_and_result_modes() {
    let _session = VerificationSession::enter();
    let integer = IntegerTerm::Variable(Variable(10993506));
    let ty = KernelMatch::test_scrutinee(vec![]).algebraic_type;
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(10993507)),
    };
    let fields = ResourceFieldValues::from_minted(vec![
        AlgebraicValue::Integer(integer),
        AlgebraicValue::Algebraic(model),
    ]);
    let integer_root = fields.retained_integer(0).unwrap().clone();
    let model_root = fields.retained_algebraic(1).unwrap().clone();
    let schema = ResourceFieldSchema::new(vec![
        ("count".into(), ResourceFieldType::Integer),
        ("model".into(), ResourceFieldType::Algebraic(ty.clone())),
    ])
    .unwrap();
    let identity = InstanceId::from_variable(Variable(10993508));
    let instance = ResourceInstance::new(
        identity,
        "LogicalProjection".into(),
        vec![].into(),
        schema,
        fields,
    )
    .unwrap();
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own(Resource::Instance(instance))),
    );
    let projection = |field_index| ResourceFieldProjection {
        identity,
        children: vec![],
        field_index,
        at_entry: false,
    };
    let mut execution = ExecutionBudget::default();
    let paths = evaluate_spec_integer_expression_paths_in(
        SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
        &SpecIntegerExpression::ResourceField(projection(0)),
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut execution),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].value.clone().into_kernel(), integer_root);
    let expression = SpecAlgebraicExpression {
        algebraic_type: ty,
        node: SpecAlgebraicExpressionNode::ResourceField(projection(1)),
    };
    for disabled in [false, true] {
        let mut execution = ExecutionBudget::default();
        let mut budget = SpecEvaluation::logical(&mut execution);
        budget.machine_result_production_disabled = disabled;
        let paths = evaluate_spec_algebraic_non_call_in(
            SpecScope::new(&state, None, &NO_ALGEBRAIC_BINDINGS),
            &expression,
            &PureFactContext::new(),
            &mut budget,
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value.root(), &model_root);
        assert_eq!(
            matches!(paths[0].value, AlgebraicResult::Imported(_)),
            disabled
        );
    }
}
