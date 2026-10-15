use super::*;

#[test]
fn logical_pointer_field_uses_current_pointee_memory() {
    use crate::kernel::{CAggregateField, CAggregateLayout};
    let slot = Pointer {
        block: "local:frame:0:input".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointee = Pointer {
        block: "local:pointee".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut entry = CState::new().with_memory(
        CMemory::new()
            .with_block(slot.block.clone(), 8)
            .with_block(pointee.block.clone(), 4)
            .store(slot.clone(), CValue::pointer(pointee.clone()))
            .store(pointee.clone(), int32(3)),
    );
    entry.locals.set_aggregate_object_at(
        "input".to_string(),
        CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
        ),
        slot.clone(),
    );
    let load = SpecExpression::MemoryLoad {
        memory: SpecMemory::Current,
        pointer: Box::new(SpecExpression::AggregateFieldValue {
            parameter: "input".to_string(),
            pointer: Box::new(SpecExpression::CExpression(CExpression::Variable(
                "input".to_string(),
            ))),
            value_type: CType::Int32Pointer,
        }),
        value_type: CType::Int32,
    };
    let state = entry.clone().with_memory(
        entry
            .memory
            .clone()
            .without_local_block(&slot.block)
            .store(pointee.clone(), int32(7)),
    );
    let evaluate = |state: &CState| {
        evaluate_spec_expression_paths_with_loop_entry_in(
            state,
            &load,
            Some(&entry),
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
        )
        .unwrap()
    };
    let paths = evaluate(&state);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].value, int32(7));
    assert!(paths[0].obligations.is_empty());
    let ended = state
        .clone()
        .with_memory(state.memory.clone().without_local_block(&pointee.block));
    let paths = evaluate(&ended);
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    assert!(!PureFactContext::new().proves_memory_read_defined(
        ended.memory(),
        &pointee,
        CType::Int32,
    ));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/aggregate_value_tests.rs");
}
