use super::*;
// A selected matched arm publishes native liveness for its actual range.
#[test]
fn wide_matched_instance_projection_keeps_native_loadability() {
    let base = Pointer::symbolic(Variable(985_700));
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Held".into(),
        fields: vec![],
    }]
    .into();
    let ty = AlgebraicType {
        rigid: false,
        name: "WideModel".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "WideModel".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let model = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Held".into(),
            fields: vec![],
        },
    };
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(985_701),
        "matched_wide".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let segment = CMemorySegment::new(
        CExpression::Value(CValue::pointer(base)),
        c_uint64_literal(0),
        c_uint64_literal(1 << 33),
    )
    .with_element_width(1);
    let mut definition =
        CCompositeResourceDefinition::new("matched_wide", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty,
        arms: vec![CResourceMatchArm {
            variant: "Held".into(),
            bindings: vec![],
            binding_types: vec![],
            binding_variables: vec![],
            contains: vec![CResourceSpec::owned_memory(segment)],
            facts: vec![],
            children: vec![],
        }],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let projection = ResourceFieldProjection {
        identity: instance.identity(),
        children: vec![],
        field_index: 0,
        at_entry: false,
    };
    let (_, facts) = matched_resource_instance_case_read_projection(
        &state,
        &projection,
        &model,
        &model,
        &[definition],
        &PureFactContext::new(),
    );
    assert!(
        facts
            .iter()
            .any(|fact| matches!(fact, Proposition::CMemoryLoadable { wide: true, .. }))
    );
}
