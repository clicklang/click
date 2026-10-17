use super::*;

#[test]
fn returned_borrows_keep_checked_entry_arguments_when_clauses_are_reordered() {
    let field = |name: &str| {
        let address = Pointer {
            block: format!("parent:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        CExpression::TypedLoad {
            pointer: Box::new(CExpression::Value(CValue::pointer(address))),
            value_type: CType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        }
    };
    let clause = |name: &str| {
        CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::Own,
            "child_ref".into(),
            vec![field(name)],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap()
    };
    let left = clause("left");
    let right = clause("right");
    let function = c_function(CType::Void, "borrow", Vec::new(), c_skip())
        .with_resource_summary(vec![left.clone(), right.clone()], vec![right, left]);
    let children = ["child:left", "child:right"].map(|name| {
        CResourceFact::own_composite(
            "child_ref".into(),
            vec![CValue::pointer(Pointer {
                block: name.into(),
                offset: PointerOffsetTerm::Constant(0),
            })],
        )
    });
    let checked = children
        .iter()
        .enumerate()
        .map(|(index, fact)| CCheckedResourceFact {
            fact: fact.clone(),
            role: CResourceTransferRole::Borrow,
            snapshot: CResourceSnapshot::Entry,
            clause_position: None,
            section_index: Some(index),
            selected_mutex_source: None,
        })
        .collect::<Vec<_>>();
    // Neither field has a materialized cell. Re-evaluating either return
    // clause would fail, even though its exact borrowed owner was checked.
    let state = CState::new();
    let returned = evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        &checked,
        &[],
        &state,
        &state,
        2,
        &[],
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        returned.facts(),
        &[children[1].clone(), children[0].clone()]
    );
}
