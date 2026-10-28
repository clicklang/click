use super::*;
use crate::kernel::{
    CAggregateField, CAggregateLayout, c_function, c_function_entry_state,
    c_parameter_with_aggregate_layout, c_return, c_void_value,
};

fn aggregate_entry(count: u32) -> (CState, BTreeMap<String, CValue>) {
    let source = Pointer {
        block: "local:caller_packet".into(),
        offset: crate::kernel::PointerOffsetTerm::Constant(0),
    };
    let layout = CAggregateLayout::new(
        8,
        8,
        vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
    );
    let value = CValue::pointer(source.clone());
    let values = (0..count)
        .map(|index| (format!("input_{index}"), value.clone()))
        .collect::<BTreeMap<_, _>>();
    let function = c_function(
        CType::Void,
        "aggregate_binding",
        values
            .keys()
            .map(|name| c_parameter_with_aggregate_layout(name, CType::VoidPointer, layout.clone()))
            .collect(),
        c_return(c_void_value()),
    );
    let caller = CState::new().with_memory(CMemory::new().with_block(source.block, 8));
    let arguments = values
        .values()
        .cloned()
        .map(CExpression::Value)
        .collect::<Vec<_>>();
    (
        c_function_entry_state(&caller, &function, &arguments).unwrap(),
        values,
    )
}

fn assert_selected_copy(selected: &FixedStateLowering, entry: &CState, current: &CState) {
    for name in ["input_0", "input_1"] {
        assert_eq!(
            selected.entry_state.locals().aggregate_object_pointer(name),
            entry.locals().aggregate_object_pointer(name),
            "entry copy of {name} was replaced by the caller argument"
        );
        assert_eq!(
            selected
                .lowering_state
                .locals()
                .aggregate_object_pointer(name),
            current.locals().aggregate_object_pointer(name),
            "current copy of {name} was replaced by the caller argument"
        );
    }
}

#[test]
fn proof_lowering_retains_each_selected_aggregate_copy() {
    let _session = crate::kernel::VerificationSession::enter();
    let (entry, values) = aggregate_entry(2);
    // Rebinding creates a different callee frame. A selected old/current
    // pair must preserve each frame independently, not use one for both.
    let source = values.values().next().unwrap().clone();
    let function = c_function(
        CType::Void,
        "nested",
        ["input_0", "input_1"]
            .into_iter()
            .map(|name| {
                c_parameter_with_aggregate_layout(
                    name,
                    CType::VoidPointer,
                    entry.locals().aggregate_layout(name).unwrap().clone(),
                )
            })
            .collect(),
        c_return(c_void_value()),
    );
    let current = c_function_entry_state(
        &entry,
        &function,
        &[
            CExpression::Value(source.clone()),
            CExpression::Value(source),
        ],
    )
    .unwrap();
    assert_ne!(
        entry.locals().aggregate_object_pointer("input_0"),
        current.locals().aggregate_object_pointer("input_0")
    );
    let arrays = ClickArrayRefs::new();
    let environment = ContractEnvironment::new(&values, &arrays);
    for preserve_places in [false, true] {
        let selected = FixedStateLowering::for_names(
            values.keys().cloned().collect(),
            environment,
            &entry,
            &current,
            None,
            preserve_places,
        );
        assert_selected_copy(&selected, &entry, &current);
    }
    let selected = FixedStateLowering::new(environment, &entry, &current, None);
    assert_selected_copy(&selected, &entry, &current);
}

#[test]
fn retired_aggregate_copy_uses_the_contract_argument_image() {
    let _session = crate::kernel::VerificationSession::enter();
    let (entry, values) = aggregate_entry(1);
    let retired = entry.clone().with_memory(CMemory::new());
    let arrays = ClickArrayRefs::new();
    let environment = ContractEnvironment::new(&values, &arrays);
    let selected = FixedStateLowering::for_names(
        values.keys().cloned().collect(),
        environment,
        &entry,
        &retired,
        None,
        false,
    );
    assert_eq!(
        selected
            .entry_state
            .locals()
            .aggregate_object_pointer("input_0"),
        entry.locals().aggregate_object_pointer("input_0")
    );
    assert_eq!(
        selected.lowering_state.locals().get("input_0"),
        values.get("input_0")
    );
    assert_eq!(
        selected.current_values.get("input_0"),
        values.get("input_0")
    );
    assert_eq!(selected.lowering_state.memory(), retired.memory());
}

#[test]
fn returned_proof_uses_argument_image_even_with_retained_private_storage() {
    let _session = crate::kernel::VerificationSession::enter();
    let (entry, values) = aggregate_entry(1);
    let arrays = ClickArrayRefs::new();
    for result in [CValue::Void, crate::kernel::int32(0)] {
        let selected = FixedStateLowering::for_names(
            values.keys().cloned().collect(),
            ContractEnvironment::new(&values, &arrays),
            &entry,
            &entry,
            Some(&result),
            false,
        );
        assert_eq!(selected.entry_values.get("input_0"), values.get("input_0"));
        assert_eq!(
            selected.current_values.get("input_0"),
            values.get("input_0")
        );
        assert_eq!(selected.lowering_state.memory(), entry.memory());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!(
        "../../../../scaling_tests/surface/proof/fixed_state_proofs/have_proofs/aggregate_binding_tests.rs"
    );
}
