use super::*;
use crate::kernel::{CResourceAccessMode, CResourceSpec, CType, c_function, int32};

#[test]
fn authority_named_memory_rewrite_preserves_population_ledger() {
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let instance = ResourceInstance::new(
        Variable(9_850_001),
        "cell".into(),
        vec![].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![],
        None,
        false,
        vec![crate::kernel::CResourceSpec::owned_memory(
            crate::kernel::CMemorySegment {
                base: CExpression::Value(CValue::pointer(crate::kernel::Pointer::symbolic(
                    Variable(9_850_002),
                ))),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                element_width: 4,
                guard: None,
            },
        )],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let function = c_function(
        CType::Int32,
        "test",
        vec![],
        CStatement::Return(CExpression::Value(int32(7))),
    )
    .with_composite_resource_definitions(vec![definition.clone()]);
    let selected = CResourceFact::own(CResource::Instance(instance.clone()));
    let folded = CState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
    let facts = ProofFacts::default();
    let (open, introduced) = crate::kernel::rewrite_resource_instance(
        &folded,
        &instance,
        &definition,
        facts.assumptions(),
        true,
    )
    .unwrap();
    let open_facts = introduced
        .into_iter()
        .fold(facts.clone(), |facts, fact| facts.with_fact(fact));
    CheckedResourceRewrite::check(
        &function,
        &folded,
        &facts,
        &selected,
        &open,
        &open_facts,
        &CheckedCallEvents::default(),
    )
    .expect("ordinary named memory is a checked representation exchange");
    let forged_facts = open_facts
        .clone()
        .with_fact(Proposition::CMemoryReadDefined {
            memory: open.memory().clone(),
            pointer: crate::kernel::Pointer::symbolic(Variable(9_850_004)),
            value_type: CType::Int32,
        });
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &folded,
            &facts,
            &selected,
            &open,
            &forged_facts,
            &CheckedCallEvents::default(),
        )
        .is_err(),
        "a named exchange cannot invent definedness of an unrelated cell"
    );
    let mut forged = open.clone();
    Arc::make_mut(&mut forged.population_effects).creation = Some(
        folded
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created(crate::kernel::PointerBlock::Heap(9_850_003)),
    );
    assert!(
        CheckedResourceRewrite::check(
            &function,
            &folded,
            &facts,
            &selected,
            &forged,
            &open_facts,
            &CheckedCallEvents::default()
        )
        .is_err(),
        "a named memory exchange cannot alter creation or population evidence"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!(
        "../../../scaling_tests/kernel/proof/execution/authority_transfer_wrapper_scaling_tests.rs"
    );
}
