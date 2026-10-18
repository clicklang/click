//! Program storage at function entry and aggregate values: static and global initialization, symbolic materialization of arrays and aggregate fields, zero initialization, and checked aggregate copies.

use super::*;

pub(super) fn initialize_c_function_globals_owned(
    mut state: CState,
    function: &CFunction,
    initialize_missing_storage: bool,
) -> CState {
    for literal in function.string_literals() {
        let slot =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_read_only_block(slot.block.clone(), literal.bytes().len() as u32),
            );
            for (offset, byte) in literal.bytes().iter().copied().enumerate() {
                if crate::instrumentation::deadline_exceeded() {
                    break;
                }
                state.set_memory(state.memory.clone().store(
                    Pointer {
                        block: slot.block.clone(),
                        offset: PointerOffsetTerm::Constant(offset as i64),
                    },
                    literal.element_value(byte),
                ));
            }
        }
        state.locals.set_array_object_at(
            literal.name().to_string(),
            literal.element_type(),
            literal.bytes().len() as u32,
            slot.clone(),
        );
        let literal_resource = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            slot,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(literal.bytes().len() as u32),
            1,
        ));
        if !function.is_program_entry()
            && !state
                .resources
                .contains_exact_representation(&literal_resource)
        {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(literal_resource);
        }
    }
    for global in function.global_variables() {
        let slot = CMemory::global_pointer(global.kernel_name());
        register_block_alignment(&slot.block, global.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global.declared_class(),
                global.c_type().byte_width(),
                global.is_constant(),
            ));
            if initialize_missing_storage || global.is_constant() {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), global.initial_value().clone()),
                );
            } else {
                state.set_memory(materialize_symbolic_cell(
                    state.memory.clone(),
                    &slot,
                    global.c_type(),
                ));
            }
        } else if !initialize_missing_storage
            && !global.is_constant()
            && global.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            // Resource setup may declare a pointer's storage before the
            // global binding is installed. Replace an untyped placeholder
            // with the authoritative typed symbolic pointer cell.
            state.set_memory(materialize_symbolic_cell(
                state.memory.clone(),
                &slot,
                global.c_type(),
            ));
        }
        state.locals.set_global_with_all_qualifiers(
            global.kernel_name().to_string(),
            global.c_type(),
            slot.clone(),
            global.is_volatile(),
            global.pointee_is_volatile(),
            global.is_constant(),
            global.pointee_is_constant(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_with_all_qualifiers(
                global.name().to_string(),
                global.c_type(),
                slot,
                global.is_volatile(),
                global.pointee_is_volatile(),
                global.is_constant(),
                global.pointee_is_constant(),
            );
        }
    }
    for global_array in function.global_arrays() {
        let slot = CMemory::global_pointer(global_array.kernel_name());
        register_block_alignment(&slot.block, global_array.element_type().abi_alignment());
        let bytes = global_array
            .length()
            .checked_mul(global_array.element_type().byte_width())
            .expect("validated C global array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_array.declared_class(),
                bytes,
                global_array.is_constant(),
            ));
            if initialize_missing_storage || global_array.is_constant() {
                state.set_memory(store_array_contents(
                    state.memory.clone(),
                    &slot,
                    global_array.element_type(),
                    global_array.initial_values(),
                ));
            } else {
                state.set_memory(materialize_symbolic_array(
                    state.memory.clone(),
                    &slot,
                    global_array.element_type(),
                    global_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_array.kernel_name().to_string(),
            global_array.element_type(),
            global_array.length(),
            slot.clone(),
            global_array.is_constant(),
        );
        if global_array.kernel_name() != global_array.name()
            && !state.locals.contains_name(global_array.name())
        {
            state.locals.set_array_object_at_with_constant(
                global_array.name().to_string(),
                global_array.element_type(),
                global_array.length(),
                slot,
                global_array.is_constant(),
            );
        }
    }
    for global_aggregate in function.global_aggregates() {
        let slot = CMemory::global_pointer(global_aggregate.kernel_name());
        register_block_alignment(&slot.block, global_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_aggregate.declared_class.clone(),
                global_aggregate.layout().size_bytes(),
                global_aggregate.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.layout(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            global_aggregate.kernel_name().to_string(),
            global_aggregate.layout().clone(),
            slot.clone(),
            global_aggregate.is_constant(),
        );
        if global_aggregate.kernel_name() != global_aggregate.source_name()
            && !state.locals.contains_name(global_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                global_aggregate.source_name().to_string(),
                global_aggregate.layout().clone(),
                slot,
                global_aggregate.is_constant(),
            );
        }
    }
    for global_aggregate_array in function.global_aggregate_arrays() {
        let slot = CMemory::global_pointer(global_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            global_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = global_aggregate_array
            .length()
            .checked_mul(global_aggregate_array.layout().size_bytes())
            .expect("validated C global aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_aggregate_array.declared_class.clone(),
                bytes,
                global_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_array(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            global_aggregate_array.is_constant(),
        );
        if global_aggregate_array.kernel_name() != global_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(global_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                global_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                global_aggregate_array.is_constant(),
            );
        }
    }
    for static_local in function.static_variables() {
        let slot = CMemory::static_pointer(function.name(), static_local.kernel_name());
        register_block_alignment(&slot.block, static_local.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_local.c_type().byte_width(),
                static_local.is_constant(),
            ));
            // A qualified resource can materialize the cell before this
            // function's storage declaration is installed. Adding block
            // metadata must not overwrite that existing value.
            if (initialize_missing_storage || static_local.is_constant())
                && state.memory.known_value(&slot).is_none()
            {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), static_local.initial_value().clone()),
                );
            } else if !initialize_missing_storage
                && !static_local.is_constant()
                && state.memory.known_value(&slot).is_none()
            {
                state.set_memory(materialize_symbolic_cell(
                    state.memory.clone(),
                    &slot,
                    static_local.c_type(),
                ));
            }
        } else if !initialize_missing_storage
            && !static_local.is_constant()
            && static_local.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            state.set_memory(materialize_symbolic_cell(
                state.memory.clone(),
                &slot,
                static_local.c_type(),
            ));
        }
        state.locals.set_global_with_all_qualifiers(
            static_local.kernel_name().to_string(),
            static_local.c_type(),
            slot.clone(),
            static_local.is_volatile(),
            static_local.pointee_is_volatile(),
            static_local.is_constant(),
            static_local.pointee_is_constant(),
        );
        // Contract C fragments use the source spelling. A nested static may
        // have a kernel-only name to distinguish it from another object in a
        // sibling block; expose the spelling only when the callee has not
        // already installed a parameter or another visible binding with it.
        if static_local.kernel_name() != static_local.source_name()
            && !state.locals.contains_name(static_local.source_name())
        {
            state.locals.set_global_with_all_qualifiers(
                static_local.source_name().to_string(),
                static_local.c_type(),
                slot,
                static_local.is_volatile(),
                static_local.pointee_is_volatile(),
                static_local.is_constant(),
                static_local.pointee_is_constant(),
            );
        }
    }
    for static_array in function.static_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_array.kernel_name());
        register_block_alignment(&slot.block, static_array.element_type().abi_alignment());
        let bytes = static_array
            .length()
            .checked_mul(static_array.element_type().byte_width())
            .expect("validated C static local array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_array.is_constant(),
            ));
            if initialize_missing_storage || static_array.is_constant() {
                state.set_memory(store_array_contents(
                    state.memory.clone(),
                    &slot,
                    static_array.element_type(),
                    static_array.initial_values(),
                ));
            } else {
                state.set_memory(materialize_symbolic_array(
                    state.memory.clone(),
                    &slot,
                    static_array.element_type(),
                    static_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_array.kernel_name().to_string(),
            static_array.element_type(),
            static_array.length(),
            slot.clone(),
            static_array.is_constant(),
        );
        if static_array.kernel_name() != static_array.source_name()
            && !state.locals.contains_name(static_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_array.source_name().to_string(),
                static_array.element_type(),
                static_array.length(),
                slot,
                static_array.is_constant(),
            );
        }
    }
    for static_aggregate in function.static_aggregates() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate.kernel_name());
        register_block_alignment(&slot.block, static_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_aggregate.layout().size_bytes(),
                static_aggregate.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.layout(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            static_aggregate.kernel_name().to_string(),
            static_aggregate.layout().clone(),
            slot.clone(),
            static_aggregate.is_constant(),
        );
        if static_aggregate.kernel_name() != static_aggregate.source_name()
            && !state.locals.contains_name(static_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                static_aggregate.source_name().to_string(),
                static_aggregate.layout().clone(),
                slot,
                static_aggregate.is_constant(),
            );
        }
    }
    for static_aggregate_array in function.static_aggregate_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            static_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = static_aggregate_array
            .length()
            .checked_mul(static_aggregate_array.layout().size_bytes())
            .expect("validated C static aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_array(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            static_aggregate_array.is_constant(),
        );
        if static_aggregate_array.kernel_name() != static_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(static_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                static_aggregate_array.is_constant(),
            );
        }
    }
    state
}

pub(super) fn materialize_symbolic_cell(
    memory: CMemory,
    pointer: &Pointer,
    c_type: CType,
) -> CMemory {
    let symbolic_base = symbolic_memory_base(&memory, pointer);
    if let Some(value) =
        crate::kernel::eval::symbolic_storage_cell_value(&symbolic_base, pointer, c_type, true)
    {
        memory.materialize_named_cell(pointer.clone(), value)
    } else {
        memory
    }
}

pub(super) fn symbolic_pointer_placeholder(value: &CValue, storage: &Pointer) -> bool {
    let CValue::Pointer(value) = value else {
        return false;
    };
    value.pointer().block == storage.block
        && !matches!(value.pointer().offset, PointerOffsetTerm::Constant(_))
}

/// Returns the stable symbolic value for a typed static-storage cell. The
/// backing memory contains only the storage block, so resource lowering and
/// ordinary function entry derive the same load identity even when the
/// caller has not yet materialized the surrounding object.
pub(super) fn symbolic_memory_base(memory: &CMemory, pointer: &Pointer) -> CMemory {
    let size = memory
        .blocks
        .get(&pointer.block)
        .and_then(|block| block.size().as_const())
        .expect("symbolic static-storage block has a constant size");
    let base = CMemory::new().with_block_without_derivation(pointer.block.clone(), size);
    // The base's block is the storage's, declared class included; otherwise
    // the storage's own snapshots and this base would name its loads apart.
    match memory.declared_class(pointer) {
        Some(class) => base.with_block_declared_class(&pointer.block, class),
        None => base,
    }
}

/// Stores `contents` into the just-declared array storage at `base`, as a
/// store of each element's value in element order leaves it, at a cost of
/// the elements the initializer wrote rather than the declared length: the
/// elements holding the default are one constant [`CellRun`], and the
/// written ones are stored over it. Where a run is refused
/// ([`CMemory::with_constant_run`]) every element is stored one by one.
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
pub(super) fn store_array_contents(
    mut memory: CMemory,
    base: &Pointer,
    element_type: CType,
    contents: &crate::kernel::CArrayContents,
) -> CMemory {
    let element =
        |index: u32| base.offset_by_bytes(index.saturating_mul(element_type.byte_width()));
    if contents.has_default_elements() {
        match memory.with_constant_run(
            base.clone(),
            element_type,
            contents.length(),
            contents.default_value().clone(),
        ) {
            Ok(mut stored) => {
                for (index, value) in contents.explicit_elements() {
                    // An explicit initializer list is as long as the source
                    // spells it; each element is a checkpoint.
                    if crate::instrumentation::deadline_exceeded() {
                        break;
                    }
                    stored = stored.store(element(*index), value.clone());
                }
                return stored;
            }
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in 0..contents.length() {
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        memory = memory.store(element(index), contents.value_at(index).clone());
    }
    memory
}

/// Every element of a symbolic static-storage array at `base` holds its
/// symbolic entry value, as [`materialize_symbolic_cell`] of each element in
/// order leaves it. The elements are one [`CellRun`] and their access widths
/// one declaration, so entry costs the same whatever `length` is; where
/// either is refused (an overlapping declaration, typed union views, a
/// block a named cell does not initialize) the elements are materialized
/// one by one.
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
pub(super) fn materialize_symbolic_array(
    mut memory: CMemory,
    base: &Pointer,
    element_type: CType,
    length: u32,
) -> CMemory {
    // Only an element type with an entry value is a run's: the others leave
    // no cell.
    let has_value = element_type.is_pointer()
        || matches!(
            element_type,
            CType::Bool
                | CType::Int8
                | CType::Int16
                | CType::Int32
                | CType::UInt8
                | CType::UInt16
                | CType::UInt32
                | CType::Int64
                | CType::Int128
                | CType::UInt64
                | CType::UInt128
                | CType::Float32
                | CType::Float64
        );
    if length > 0 && has_value {
        let source = crate::kernel::intern_c_memory(symbolic_memory_base(&memory, base));
        // An object pointer's load records no width, so it declares none.
        let widths_declared = element_type.is_object_pointer()
            || crate::kernel::eval::declare_symbolic_array_access_widths(
                &source,
                base,
                element_type.byte_width(),
                length,
                element_type.byte_width(),
            );
        if widths_declared {
            match memory.with_symbolic_storage_run(base.clone(), element_type, length, source) {
                Ok(materialized) => return materialized,
                Err(unchanged) => memory = unchanged,
            }
        }
    }
    for index in 0..length {
        // A checkpoint per element: a stopped run keeps the partial memory
        // only until its caller's next checkpoint reports the limit.
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        let pointer = base.offset_by_bytes(index.saturating_mul(element_type.byte_width()));
        memory = materialize_symbolic_cell(memory, &pointer, element_type);
    }
    memory
}

pub(super) fn materialize_symbolic_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let field_base = base.offset_by_bytes(field.offset_bytes());
        match field.c_type() {
            CType::Int32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Int32, length);
            }
            CType::Int64Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Int64, length);
            }
            CType::Int128Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Int128, length);
            }
            CType::UInt64Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::UInt64, length);
            }
            CType::UInt128Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::UInt128, length);
            }
            CType::UInt8Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::UInt8, length);
            }
            CType::Float32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float32, length);
            }
            CType::Float64Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float64, length);
            }
            _ => {
                memory = materialize_symbolic_cell(memory, &field_base, field.c_type());
            }
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        let views = union
            .fields()
            .iter()
            .filter_map(|field| {
                let pointer = union_base.offset_by_bytes(field.offset_bytes());
                let symbolic_base = symbolic_memory_base(&memory, &pointer);
                symbolic_load_value(&symbolic_base, &pointer, field.c_type())
                    .map(|value| (pointer, field.c_type(), value))
            })
            .collect();
        memory = memory.store_union_views(union_base, union.size_bytes(), views);
    }
    memory
}

/// Whether a symbolic static-storage cell of `c_type` holds an entry value:
/// the element types [`materialize_symbolic_array`] makes a run of.
pub(super) fn symbolic_storage_has_value(c_type: CType) -> bool {
    c_type.is_pointer()
        || matches!(
            c_type,
            CType::Bool
                | CType::Int8
                | CType::Int16
                | CType::Int32
                | CType::UInt8
                | CType::UInt16
                | CType::UInt32
                | CType::Int64
                | CType::Int128
                | CType::UInt64
                | CType::UInt128
                | CType::Float32
                | CType::Float64
        )
}

/// The cells [`materialize_symbolic_aggregate_fields`] names in one struct
/// of `layout`, as `(offset, type)` ascending: each scalar field, and each
/// element of an inline scalar array field. `None` for a layout with unions
/// or with a field kind that routine does not name this way.
pub(super) fn symbolic_aggregate_cells(layout: &CAggregateLayout) -> Option<Vec<(u32, CType)>> {
    if !layout.unions().is_empty() {
        return None;
    }
    let mut cells = Vec::new();
    for field in layout.fields() {
        let (element_type, length) = match field.c_type() {
            CType::Int32Array(length) => (CType::Int32, length),
            CType::Int64Array(length) => (CType::Int64, length),
            CType::Int128Array(length) => (CType::Int128, length),
            CType::UInt64Array(length) => (CType::UInt64, length),
            CType::UInt128Array(length) => (CType::UInt128, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Float32Array(length) => (CType::Float32, length),
            CType::Float64Array(length) => (CType::Float64, length),
            c_type if symbolic_storage_has_value(c_type) => (c_type, 1),
            _ => return None,
        };
        for index in 0..length {
            // A stopped run takes the element-by-element fallback, whose
            // own checkpoints report the limit.
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            cells.push((
                field
                    .offset_bytes()
                    .checked_add(index.checked_mul(element_type.byte_width())?)?,
                element_type,
            ));
        }
    }
    cells.sort_by_key(|(offset, _)| *offset);
    Some(cells)
}

/// Every struct of a symbolic static-storage array of `length` structs at
/// `base` holds its fields' symbolic entry values, as
/// [`materialize_symbolic_aggregate_fields`] of each struct in order leaves
/// them. Each field is one [`CellRun`] stepping by the struct's size, and
/// the fields' access widths are one declaration, so entry costs the
/// layout rather than the struct count; where either is refused, or the
/// layout has more cells than there are structs, the structs are
/// materialized one by one.
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
pub(super) fn materialize_symbolic_aggregate_array(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    if let Some(cells) = symbolic_aggregate_cells(layout)
        && !cells.is_empty()
        && cells.len() <= length as usize
    {
        let source = crate::kernel::intern_c_memory(symbolic_memory_base(&memory, base));
        // An object pointer's load records no width, so it declares none.
        let widths = cells
            .iter()
            .filter(|(_, c_type)| !c_type.is_object_pointer())
            .map(|(offset, c_type)| (*offset, c_type.byte_width()))
            .collect::<Vec<_>>();
        let widths_declared = widths.is_empty()
            || crate::kernel::eval::declare_symbolic_element_access_widths(
                &source,
                base,
                layout.size_bytes(),
                length,
                &widths,
            );
        if widths_declared {
            match memory.with_symbolic_storage_runs(
                base,
                layout.size_bytes(),
                length,
                &cells,
                source,
            ) {
                Ok(materialized) => return materialized,
                Err(unchanged) => memory = unchanged,
            }
        }
    }
    for index in 0..length {
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate symbolic offset"),
        );
        memory = materialize_symbolic_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

/// The zero-initialized scalar fields of `layout`, as static storage holds
/// them before any initializer: each field's byte offset, how many elements
/// it holds (one, or an inline array's length), each element's width, and
/// the zero every element holds. A field kind with no modeled zero is left
/// out, as it is left without a cell. Unions are not included.
pub(super) fn aggregate_zero_fields(layout: &CAggregateLayout) -> Vec<(u32, u32, u32, CValue)> {
    let mut zero_fields = Vec::with_capacity(layout.fields().len());
    for field in layout.fields() {
        let (element_type, element_count) = match field.c_type() {
            CType::Int8 => (field.c_type(), 1),
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
                | CType::Int128
            | CType::UInt64
                | CType::UInt128
            | CType::Float32
            | CType::Float64
            | CType::VoidPointer
            | CType::Int128Pointer
            | CType::UInt128Pointer
            | CType::Int128PointerPointer
            | CType::UInt128PointerPointer
            | CType::Int32Pointer
            | CType::UInt8Pointer
            // A signed plain `char` pointer field is an `int8*` cell.
            | CType::Int8Pointer
            | CType::Float32Pointer
            | CType::Float64Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::Int8PointerPointer
            | CType::Float32PointerPointer
            | CType::Float64PointerPointer
            // Static storage zero-initializes a callback field to a null
            // function pointer, just like a data-pointer field.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            // A signed plain `char` array field holds `int8` cells.
            CType::Int8Array(length) => (CType::Int8, length),
            CType::Int64Array(length) => (CType::Int64, length),
            CType::Int128Array(length) => (CType::Int128, length),
            CType::UInt64Array(length) => (CType::UInt64, length),
            CType::UInt128Array(length) => (CType::UInt128, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Float32Array(length) => (CType::Float32, length),
            CType::Float64Array(length) => (CType::Float64, length),
            CType::PointerArray(element, length) => (element.pointer_type(), length),
            _ => continue,
        };
        let zero = if matches!(field.c_type(), CType::PointerArray(_, _)) {
            CValue::typed_pointer(Pointer::null(), element_type)
        } else {
            match element_type {
                CType::Parameter(_) => unreachable!("an array element is a machine type"),
                CType::Bool => CValue::Bool(Bitvector32Term::Constant(0)),
                CType::Int8 => int8(0),
                CType::Int16 => int16(0),
                CType::Int32 => int32(0),
                CType::UInt8 => uint8(0),
                CType::UInt16 => uint16(0),
                CType::UInt32 => uint32(0),
                CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(0)),
                CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
                CType::Int128 => MachineIntegerType::Int128
                    .constant_value(
                        MachineIntegerConstant::from_signed(MachineIntegerType::Int128.format(), 0)
                            .unwrap(),
                    )
                    .unwrap(),
                CType::UInt128 => MachineIntegerType::UInt128
                    .constant_value(
                        MachineIntegerConstant::from_unsigned(
                            MachineIntegerType::UInt128.format(),
                            0,
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                CType::Float32 => CValue::Float32(Bitvector32Term::Constant(0)),
                CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(0)),
                CType::Int128Pointer
                | CType::UInt128Pointer
                | CType::Int128PointerPointer
                | CType::UInt128PointerPointer
                | CType::Int32Pointer
                | CType::UInt8Pointer
                | CType::Int8Pointer
                | CType::Float32Pointer
                | CType::Float64Pointer
                | CType::Int32PointerPointer
                | CType::UInt8PointerPointer
                | CType::Int8PointerPointer
                | CType::Float32PointerPointer
                | CType::Float64PointerPointer
                | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), element_type),
                CType::Int8Array(_) => {
                    continue;
                }
                CType::PointerArray(_, _) => continue,
                CType::Int16Array(_)
                | CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int128Array(_)
                | CType::Int64Array(_)
                | CType::UInt128Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Array(_)
                | CType::Float64Array(_)
                | CType::Void
                | CType::VoidPointer
                | CType::VoidPointerPointer => {
                    continue;
                }
                CType::Int16Pointer
                | CType::UInt16Pointer
                | CType::UInt32Pointer
                | CType::Int64Pointer
                | CType::UInt64Pointer
                | CType::Int16PointerPointer
                | CType::UInt16PointerPointer
                | CType::UInt32PointerPointer
                | CType::Int64PointerPointer
                | CType::UInt64PointerPointer => continue,
            }
        };
        zero_fields.push((
            field.offset_bytes(),
            element_count,
            element_type.byte_width(),
            zero,
        ));
    }
    zero_fields
}

pub(super) fn zero_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for (field_offset, element_count, element_width, zero) in aggregate_zero_fields(layout) {
        for index in 0..element_count {
            if crate::instrumentation::deadline_exceeded() {
                break;
            }
            let offset = field_offset
                .checked_add(
                    index
                        .checked_mul(element_width)
                        .expect("validated aggregate zero field offset"),
                )
                .expect("validated aggregate zero field offset");
            memory = memory.store(base.offset_by_bytes(offset), zero.clone());
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        let views = union
            .fields()
            .iter()
            .filter_map(|field| {
                zero_union_member_value(field.c_type()).map(|value| {
                    (
                        union_base.offset_by_bytes(field.offset_bytes()),
                        field.c_type(),
                        value,
                    )
                })
            })
            .collect();
        memory = memory.store_union_views(union_base, union.size_bytes(), views);
    }
    memory
}

pub(super) fn zero_union_member_value(c_type: CType) -> Option<CValue> {
    Some(match c_type {
        CType::Int32 => int32(0),
        CType::UInt8 => uint8(0),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), c_type),
        _ => return None,
    })
}

pub(super) fn initialize_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    initializers: &[CAggregateInitializer],
) -> CMemory {
    for initializer in initializers {
        memory = memory.store(
            base.offset_by_bytes(initializer.offset_bytes()),
            initializer.value().clone(),
        );
    }
    memory
}

/// The zero contents of `length` consecutive structs of `layout`, as
/// constant runs: a scalar field is one run over every element, stepping by
/// the struct's size, and an inline array field of `n` elements is `n` such
/// runs or, when the array is the longer of the two, one run per struct
/// stepping by the field's element width. So the runs cost the layout, and
/// never more than the struct count per array field, rather than the
/// struct count times the layout. `None` for a layout with unions, whose
/// zero views are typed overlays a run does not stand for.
pub(super) fn aggregate_array_zero_runs(
    layout: &CAggregateLayout,
    length: u32,
) -> Option<Vec<CConstantRun>> {
    if !layout.unions().is_empty() || layout.size_bytes() == 0 {
        return None;
    }
    let stride = layout.size_bytes();
    let mut runs = Vec::new();
    for (field_offset, element_count, element_width, zero) in aggregate_zero_fields(layout) {
        if element_count <= length {
            for index in 0..element_count {
                // As in `symbolic_aggregate_cells`: a stopped run falls back
                // to the checkpointed element-by-element zeroing.
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                runs.push(CConstantRun {
                    offset: field_offset.checked_add(index.checked_mul(element_width)?)?,
                    stride,
                    count: length,
                    value: zero.clone(),
                });
            }
        } else {
            for element in 0..length {
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                runs.push(CConstantRun {
                    offset: element.checked_mul(stride)?.checked_add(field_offset)?,
                    stride: element_width,
                    count: element_count,
                    value: zero.clone(),
                });
            }
        }
    }
    Some(runs)
}

pub(super) fn zero_aggregate_array_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    if let Some(runs) = aggregate_array_zero_runs(layout, length) {
        match memory.with_constant_runs(base, &runs) {
            Ok(filled) => return filled,
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in 0..length {
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate array zero offset"),
        );
        memory = zero_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

/// Copy the modeled cells of an address-backed aggregate into a distinct
/// destination block. Fixed scalar-array fields and flattened embedded-struct
/// array leaves are copied one cell at a time. Pointer fields are
/// shallow-copied: the pointer value is duplicated,
/// but the pointed-to allocation is not. Missing cells in automatic storage
/// remain missing so an uninitialized source field stays uninitialized in the
/// copy; opaque/external source cells are represented by typed symbolic loads.
/// Whether a borrowed local view names storage its block actually has.
///
/// Only a range whose bounds are constant can be placed against the block's
/// extent. One with symbolic bounds keeps the previous treatment: it is the
/// caller's own stack object either way, and tightening that case belongs
/// with the range-arithmetic work rather than here.
pub(super) fn local_view_range_within_block(range: &CMemoryRange, memory: &CMemory) -> bool {
    // Signed, both endpoints. `as_const` answers `u32`, so a start of `-1`
    // arrived as `4294967295` and `end <= start` short-circuited to "in
    // bounds" for every range that begins below its block — the exact
    // opposite of what this asks. `pair[-1..3]` was placed inside a
    // two-element local while the contained `pair[0..3]` was refused.
    let (Some(start), Some(end)) = (range.signed_constant_start(), range.signed_constant_end())
    else {
        return true;
    };
    // An empty range names no storage, and `end < start` is how a range says
    // so: `memory_range_byte_count` scales the signed count, so this is the
    // same reading the extent guards use.
    if end <= start {
        return true;
    }
    let Some(bytes) = end
        .checked_sub(start)
        .and_then(|count| count.checked_mul(i64::from(range.element_width())))
        .and_then(|bytes| u32::try_from(bytes).ok())
    else {
        return false;
    };
    let base = range.start_pointer();
    memory.access_in_bounds(&base, bytes)
}

/// Check actual argument reads before allocating the callee's private copy.
pub(super) fn aggregate_argument_read_refusal(
    state: &CState,
    parameters: &[CParameter],
    values: &[CValue],
    assumptions: &PureFactContext,
) -> Option<CFunctionOutcome> {
    for (parameter, value) in parameters.iter().zip(values) {
        let Some(layout) = parameter.aggregate_layout() else {
            continue;
        };
        let CValue::Pointer(source) = value else {
            continue;
        };
        if let Some(refusal) = crate::kernel::eval::subobject_access_refusal(
            source.pointer(),
            source.extent(),
            layout.size_bytes(),
            &ExecutionFacts::new(),
            &[],
            assumptions,
        ) {
            return Some(CFunctionOutcome::UndefinedBehavior(refusal));
        }
        // Actual calls use the same read boundary as ordinary aggregate
        // assignment. Entry images are evaluated values, not caller reads.
        if let Some(resource) = crate::kernel::eval::missing_aggregate_copy_read_resource(
            state,
            source,
            layout,
            assumptions,
        ) {
            return Some(CFunctionOutcome::RuntimeError(
                CRuntimeError::MissingResource {
                    resource: Box::new(resource),
                },
            ));
        }
        if aggregate_copy_reads_uninitialized(&state.memory, source.pointer(), layout) {
            return Some(CFunctionOutcome::UndefinedBehavior(
                CUndefinedBehavior::UninitializedRead,
            ));
        }
    }
    None
}

/// Whole-struct assignment copies every member (C11 6.5.16.1p2), but
/// `copy_aggregate_fields` skips a carried field with no source cell. Copying
/// from never-written source storage would then leave the destination's own
/// cell in place and readable. Every aggregate-copy path (direct assignment,
/// return materialization, return assignment) reports that skipped read as an
/// uninitialized read instead, matching what member-wise assignment reports
/// through the ordinary load path.
pub(super) fn aggregate_copy_reads_uninitialized(
    memory: &CMemory,
    source: &Pointer,
    layout: &CAggregateLayout,
) -> bool {
    // Mirror the carried-field classification in `copy_aggregate_fields`: a
    // field type this copy cannot carry drops the destination cells instead
    // of leaving them readable, so it cannot go stale here.
    for field in layout.fields() {
        if let CType::UInt32Array(count) = field.c_type() {
            let source_field = source.offset_by_bytes(field.offset_bytes());
            let Some(bytes) = count.checked_mul(4) else {
                return true;
            };
            if bytes == 0
                || memory.has_initialized_bytes_under(&source_field, bytes, &PureFactContext::new())
                || memory.is_zeroed_heap_address(&source_field, bytes, &PureFactContext::new())
            {
                continue;
            }
            if memory.may_read_uninitialized_object(&source_field, bytes)
                || memory.is_uninitialized_heap_address(
                    &source_field,
                    bytes,
                    &PureFactContext::new(),
                )
                || (source_field.block.is_local_block()
                    && memory.access_in_bounds(&source_field, bytes))
            {
                return true;
            }
        }

        let (element_type, element_count) = match field.c_type() {
            CType::Int8 => (field.c_type(), 1),
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::Int128
            | CType::UInt64
            | CType::UInt128
            | CType::Float32
            | CType::Float64 => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt32Array(length) => (CType::UInt32, length),
            CType::Int64Array(length) => (CType::Int64, length),
            CType::Int128Array(length) => (CType::Int128, length),
            CType::UInt64Array(length) => (CType::UInt64, length),
            CType::UInt128Array(length) => (CType::UInt128, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            _ => continue,
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            if uninitialized_aggregate_copy_source_cell(
                memory,
                &source.offset_by_bytes(element_offset),
                element_type,
            ) {
                return true;
            }
        }
    }
    for union in layout.unions() {
        let union_source = source.offset_by_bytes(union.offset_bytes());
        // A union with any readable member is initialized storage: the copy
        // carries the active member view and skips the rest, so no member
        // read is uninitialized. Only a wholly unread union can leave the
        // destination holding a stale cell.
        let union_initialized = union.fields().iter().any(|field| {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            // Mirror `copy_aggregate_union_member`: a value stored through
            // any member is carried.
            memory
                .known_union_value(&source_field, field.c_type())
                .is_some()
                || memory
                    .known_value(&source_field)
                    .is_some_and(|value| field.c_type().accepts(&value))
                // A member whose cached view was forgotten but whose bytes
                // the initialization record holds was written all the same.
                || memory.has_initialized_bytes_at(&source_field, field.c_type().byte_width())
        });
        if union_initialized {
            continue;
        }
        for field in union.fields() {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            if uninitialized_aggregate_copy_source_cell(memory, &source_field, field.c_type()) {
                return true;
            }
        }
    }
    false
}

/// Mirrors the silent skip in `copy_aggregate_fields`: no source cell, bytes
/// the initialization record does not hold, and not a zeroed heap address.
/// Reading such a cell is a read of uninitialized
/// storage when the address is a live local or an uninitialized heap cell;
/// anything else (external or symbolic memory) reads back as an unconstrained
/// symbolic load rather than stale storage.
pub(super) fn uninitialized_aggregate_copy_source_cell(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> bool {
    if memory.known_value(source_field).is_some()
        || memory.has_initialized_bytes_at(source_field, element_type.byte_width())
    {
        return false;
    }
    if memory.is_zeroed_heap_address(
        source_field,
        element_type.byte_width(),
        &PureFactContext::new(),
    ) {
        return false;
    }
    memory.may_read_uninitialized_object(source_field, element_type.byte_width())
        || memory.is_uninitialized_heap_address(
            source_field,
            element_type.byte_width(),
            &PureFactContext::new(),
        )
        || (source_field.block.is_local_block()
            && memory.access_in_bounds(source_field, element_type.byte_width()))
}

/// Whether a copy's source field is storage of this memory that holds no
/// value the copy can carry: a block it allocates (not symbolic or temporary
/// storage), in bounds, with no cached value or zero guarantee (the callers
/// ask those first) and with bytes the initialization record does not hold.
/// The copy skips such a field, and `aggregate_copy_reads_uninitialized`
/// has already refused it where it is uninitialized. A field whose cached
/// value was forgotten (by a store the facts could not place, or a loop,
/// call or join havoc) but whose bytes the record holds was written all the
/// same: the copy carries its unknown value as the typed load of the source,
/// as for external storage, so the destination is initialized too.
pub(super) fn aggregate_copy_source_holds_nothing(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> bool {
    memory.has_block(&source_field.block)
        && !matches!(
            source_field.block,
            PointerBlock::Symbolic(_) | PointerBlock::Temporary(_)
        )
        && memory.access_in_bounds(source_field, element_type.byte_width())
        && !memory.has_initialized_bytes_at(source_field, element_type.byte_width())
}

/// Every aggregate-copy path goes through this wrapper so a copy from
/// uninitialized source storage is reported as an uninitialized read instead
/// of silently keeping the destination's old value. The raw
/// `copy_aggregate_fields` is deliberately module-private; new call sites in
/// other modules must use this checked form.
pub(in crate::kernel) fn copy_aggregate_fields_checked(
    memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> Result<CMemory, CUndefinedBehavior> {
    if aggregate_copy_reads_uninitialized(&memory, source, layout) {
        return Err(CUndefinedBehavior::UninitializedRead);
    }
    Ok(copy_aggregate_fields(memory, source, destination, layout))
}

// Module-private on purpose: cross-module aggregate copies must go through
// `copy_aggregate_fields_checked` so the uninitialized-source read is always
// reported. Actual call arguments are checked before binding; entry proof
// images use the raw form because their incoming aggregate values are evaluated.
pub(super) fn copy_aggregate_fields(
    mut memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        if let CType::UInt32Array(count) = field.c_type() {
            let source_field = source.offset_by_bytes(field.offset_bytes());
            let target_field = destination.offset_by_bytes(field.offset_bytes());
            if let Ok(copied) = memory.clone().write_scalar_array_region(
                &target_field,
                CType::UInt32,
                count,
                CValue::typed_pointer(source_field, CType::UInt32Pointer),
                true,
                false,
                &PureFactContext::new(),
            ) {
                memory = copied;
                continue;
            }
            // Forgotten initialized values stay an immutable typed snapshot,
            // without generating one load for each element of the field.
            if let Ok(copied) = memory.clone().write_scalar_array_snapshot(
                &target_field,
                CType::UInt32,
                count,
                CValue::typed_pointer(
                    source.offset_by_bytes(field.offset_bytes()),
                    CType::UInt32Pointer,
                ),
                true,
                false,
                &PureFactContext::new(),
            ) {
                memory = copied;
                continue;
            }
        }

        let (element_type, element_count) = match field.c_type() {
            CType::Int8 => (field.c_type(), 1),
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
                | CType::Int128
            | CType::UInt64
                | CType::UInt128
            | CType::Float32
            | CType::Float64
            // A generic struct's field of an abstract type parameter.
            | CType::Parameter(_) => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt32Array(length) => (CType::UInt32, length),
            CType::Int64Array(length) => (CType::Int64, length),
            CType::Int128Array(length) => (CType::Int128, length),
            CType::UInt64Array(length) => (CType::UInt64, length),
            CType::UInt128Array(length) => (CType::UInt128, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            // A callback field is an eight-byte pointer value; carry it so a
            // copied table still dispatches to the same concrete target.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            // A field this copy cannot carry must not leave the destination's
            // previous value in place: C copies every member, so a stale cell
            // would be readable as the destination's old contents. Drop those
            // cells instead, which reads back as unknown rather than wrong.
            unsupported => {
                memory = memory.without_field_cells(destination, field.offset_bytes(), unsupported);
                continue;
            }
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            let source_field = source.offset_by_bytes(element_offset);
            let destination_field = destination.offset_by_bytes(element_offset);
            let value = memory.known_value(&source_field).or_else(|| {
                if memory.is_zeroed_heap_address(
                    &source_field,
                    element_type.byte_width(),
                    &PureFactContext::new(),
                ) {
                    return match element_type {
                        CType::Int8 => Some(int8(0)),
                        CType::Int16 => Some(int16(0)),
                        CType::Int32 => Some(int32(0)),
                        CType::UInt8 => Some(uint8(0)),
                        CType::Int32Pointer
                        | CType::UInt8Pointer
                        | CType::Int32PointerPointer
                        | CType::UInt8PointerPointer => {
                            Some(CValue::typed_pointer(Pointer::null(), element_type))
                        }
                        CType::UInt16 => Some(uint16(0)),
                        CType::UInt32 => Some(uint32(0)),
                        CType::Int64 => Some(CValue::Int64(Bitvector32Term::Int64Constant(0))),
                        CType::UInt64 => Some(CValue::UInt64(Bitvector32Term::UInt64Constant(0))),
                        CType::Float32 => Some(CValue::Float32(Bitvector32Term::Constant(0))),
                        CType::Float64 => Some(CValue::Float64(Bitvector32Term::UInt64Constant(0))),
                        _ => None,
                    };
                }
                if aggregate_copy_source_holds_nothing(&memory, &source_field, element_type) {
                    return None;
                }
                match element_type {
                    CType::Int8 => Some(CValue::Int8(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Int16 => Some(CValue::Int16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Int32 => Some(CValue::Int32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::UInt8 => Some(CValue::UInt8(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::Int32PointerPointer
                    | CType::UInt8PointerPointer => {
                        // An unknown pointer is the value read from this cell,
                        // not an offset in the object holding it. Use the same
                        // canonical typed read as ordinary pointer loads so a
                        // trivial copy preserves provenance and checked aliases.
                        crate::kernel::eval::symbolic_storage_cell_value(
                            &memory,
                            &source_field,
                            element_type,
                            true,
                        )
                    }
                    CType::UInt16 => Some(CValue::UInt16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::UInt32 => Some(CValue::UInt32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Int64 => Some(CValue::Int64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::UInt64 => Some(CValue::UInt64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Float32 => Some(CValue::Float32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Float64 => Some(CValue::Float64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                        LoadKind::of_type(element_type)?,
                    ))),
                    CType::Parameter(_) => crate::kernel::eval::symbolic_load_value_unrecorded(
                        &memory,
                        &source_field,
                        element_type,
                    ),
                    _ => None,
                }
            });
            if let Some(value) = value {
                memory = memory.store(destination_field, value);
            }
        }
    }
    for union in layout.unions() {
        let source_union = source.offset_by_bytes(union.offset_bytes());
        let destination_union = destination.offset_by_bytes(union.offset_bytes());
        let views = union
            .fields()
            .iter()
            .filter_map(|field| {
                let source_field = source_union.offset_by_bytes(field.offset_bytes());
                copy_aggregate_union_member(&memory, &source_field, field.c_type()).map(|value| {
                    (
                        destination_union.offset_by_bytes(field.offset_bytes()),
                        field.c_type(),
                        value,
                    )
                })
            })
            .collect();
        memory = memory.store_union_views(destination_union, union.size_bytes(), views);
    }
    memory
}

pub(super) fn copy_aggregate_union_member(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> Option<CValue> {
    if let Some(value) = memory.known_union_value(source_field, element_type) {
        return Some(value);
    }
    if let Some(value) = memory.known_value(source_field)
        && element_type.accepts(&value)
    {
        return Some(value);
    }
    if memory.is_zeroed_heap_address(
        source_field,
        element_type.byte_width(),
        &PureFactContext::new(),
    ) {
        return zero_union_member_value(element_type);
    }
    if aggregate_copy_source_holds_nothing(memory, source_field, element_type) {
        return None;
    }
    let load = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_c_memory(memory.clone()),
        source_field.clone(),
        LoadKind::of_type(element_type)?,
    );
    Some(match element_type {
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => {
            let pointer = if matches!(element_type, CType::FunctionPointer(_)) {
                match load {
                    Bitvector32Term::Variable(variable) => Pointer::symbolic_function(variable),
                    load => Pointer {
                        block: source_field.block.clone(),
                        offset: PointerOffsetTerm::scale_int32(load, 1),
                    },
                }
            } else {
                let pointee_type = element_type.pointee_type()?;
                Pointer {
                    block: source_field.block.clone(),
                    offset: PointerOffsetTerm::scale_int32(
                        load,
                        i64::from(pointee_type.byte_width()),
                    ),
                }
            };
            CValue::typed_pointer(pointer, element_type)
        }
        _ => return None,
    })
}
