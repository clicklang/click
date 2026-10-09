//! Exact destination binding for the initial complete-object construction slice.
use super::*;

fn valid_layout(layout: &CAggregateLayout) -> bool {
    if layout.size_bytes() == 0
        || !layout.size_bytes().is_multiple_of(layout.alignment_bytes())
        || !layout.unions().is_empty()
    {
        return false;
    }
    let mut end = 0;
    for field in layout.fields() {
        crate::instrumentation::record_deterministic_work(1);
        let ty = field.c_type();
        let scalar = ty.is_pointer()
            || matches!(
                ty,
                CType::Bool
                    | CType::Int8
                    | CType::UInt8
                    | CType::Int16
                    | CType::UInt16
                    | CType::Int32
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
                    | CType::Int128
                    | CType::UInt128
                    | CType::Float32
                    | CType::Float64
            );
        if !scalar
            || field.offset_bytes() < end
            || !field.offset_bytes().is_multiple_of(ty.abi_alignment())
            || layout.alignment_bytes() < ty.abi_alignment()
        {
            return false;
        }
        let Some(next) = field.offset_bytes().checked_add(ty.byte_width()) else {
            return false;
        };
        if next > layout.size_bytes() {
            return false;
        }
        end = next;
    }
    true
}

fn destination<'a>(
    state: &'a CState,
    interface: &CFunctionContractInterface,
) -> Option<&'a CAggregateDestination> {
    let selected = state.aggregate_destination.as_deref()?;
    let layout = interface.return_aggregate_layout()?;
    if interface.aggregate_return_mode() != CAggregateReturnMode::Construction
        || !interface.exceptional_signature().is_empty()
        || !interface.return_type().is_pointer()
        || selected.layout != *layout
        || !valid_layout(layout)
        || selected.pointer.offset != PointerOffsetTerm::Constant(0)
        || state.memory.block_size(&selected.pointer.block) != Some(&layout.size_bytes().into())
        || state.memory.is_read_only_block(&selected.pointer.block)
        || registered_block_alignment(&selected.pointer.block)?
            < u64::from(layout.alignment_bytes())
        || !(selected.pointer.block.starts_with("local:")
            || state
                .memory
                .heap
                .uninitialized_objects
                .get(&selected.pointer)
                == Some(&layout.size_bytes()))
    {
        return None;
    }
    Some(selected)
}

pub(super) fn bind(
    caller: &CState,
    interface: &CFunctionContractInterface,
    callee: &mut CState,
) -> Option<()> {
    if interface.aggregate_return_mode() == CAggregateReturnMode::Copy {
        return Some(());
    }
    let selected = destination(caller, interface)?;
    if interface
        .parameters()
        .iter()
        .any(|parameter| parameter.name() == C_CONTRACT_RESULT_NAME)
        || caller
            .resources
            .memory_write_range(
                &selected.pointer,
                selected.layout.size_bytes(),
                &PureFactContext::new(),
            )
            .is_none()
        || crate::kernel::eval::memory_write_permission_outcome(
            caller,
            &selected.pointer,
            selected.layout.size_bytes(),
            &PureFactContext::new(),
        )
        .is_some()
    {
        return None;
    }
    callee.aggregate_destination = caller.aggregate_destination.clone();
    callee.locals.set_aggregate_object_at(
        C_CONTRACT_RESULT_NAME,
        selected.layout.clone(),
        selected.pointer.clone(),
    );
    Some(())
}

pub(super) fn complete(
    state: &CState,
    interface: &CFunctionContractInterface,
    value: CValue,
) -> Result<CValue, AggregateReturnRefusal> {
    let selected = destination(state, interface).ok_or(AggregateReturnRefusal::InvalidValue)?;
    let CValue::Pointer(pointer) = &value else {
        return Err(AggregateReturnRefusal::InvalidValue);
    };
    if pointer.pointer() != &selected.pointer
        || state
            .locals
            .aggregate_object_pointer(C_CONTRACT_RESULT_NAME)
            != Some(&selected.pointer)
    {
        return Err(AggregateReturnRefusal::InvalidValue);
    }
    if aggregate_copy_reads_uninitialized(&state.memory, &selected.pointer, &selected.layout) {
        return Err(AggregateReturnRefusal::UninitializedRead);
    }
    Ok(value)
}

pub(super) fn summary_result(
    state: &CState,
    interface: &CFunctionContractInterface,
) -> Option<CValue> {
    let selected = destination(state, interface)?;
    Some(CValue::typed_pointer(
        selected.pointer.clone(),
        interface.return_type(),
    ))
}

/// Only a body-certified construction rule justifies these initialized fields.
/// The call's existing effect transition forgets their old values first.
pub(super) fn initialize_summary(state: &mut CState, interface: &CFunctionContractInterface) {
    let selected = state
        .aggregate_destination
        .as_ref()
        .expect("checked destination")
        .clone();
    for field in interface
        .return_aggregate_layout()
        .expect("construction layout")
        .fields()
    {
        let pointer = selected.pointer.offset_by_bytes(field.offset_bytes());
        state.set_memory(
            state
                .memory
                .clone()
                .with_initialized_object(&pointer, field.c_type().byte_width()),
        );
    }
}
