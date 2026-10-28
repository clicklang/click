use super::*;

fn entry_state() -> CState {
    use crate::kernel::*;
    let source = Pointer {
        block: "local:caller".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let function = c_function(
        CType::Void,
        "copy",
        vec![c_parameter_with_aggregate_layout(
            "input",
            CType::VoidPointer,
            CAggregateLayout::new(
                8,
                8,
                vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
            ),
        )],
        c_return(c_void_value()),
    );
    c_function_entry_state(
        &CState::new().with_memory(CMemory::new().with_block(source.block.clone(), 8)),
        &function,
        &[CExpression::Value(CValue::pointer(source))],
    )
    .unwrap()
}

fn lower_name(state: &CState, name: &str, at_entry: bool) -> Result<SpecExpression, String> {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let snapshots = RecordedSnapshots::new();
    let (lowerer, _) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    lowerer.lower_c_binding_to_spec(
        name,
        &SpecElaborationContext {
            current_memory: SpecMemory::Fixed(state.memory().clone()),
            at_function_entry: at_entry,
            ..Default::default()
        },
    )
}

#[test]
fn old_aggregate_binding_uses_only_the_selected_entry_place() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = entry_state();
    assert_eq!(
        lower_name(&state, "input", true).unwrap(),
        SpecExpression::Value(CValue::typed_pointer(
            state
                .locals()
                .aggregate_object_pointer("input")
                .unwrap()
                .clone(),
            CType::UInt8Pointer
        ))
    );
    assert!(lower_name(&state, "later_local", true).is_err());
    assert!(lower_name(&state, "input", false).is_err());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/lowering/annotations/old_aggregate_tests.rs");
}
