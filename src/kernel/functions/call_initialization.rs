//! A contract's plain memory clause holds initialized bytes.
//!
//! `owns p[a..b]`, `views p[a..b]`, and `consumes p[a..b]` say the callee may
//! read the range: its proof starts with those bytes initialized. A caller
//! that supplies storage with an initialization history (an automatic object,
//! fresh `malloc` storage, a range it holds as `uninitialized(...)`) must have
//! initialized every byte first. A callee that writes the range before it
//! reads it holds it as `uninitialized(p[a..b])` instead, which this check
//! skips. Memory with no initialization history, such as the caller's own
//! input ranges, is initialized by its own contract.

use super::*;

/// A range wider than this many elements is decided by its initialization
/// record alone: per-element `defined` evidence is looked up only for ranges
/// this small, so the work stays proportional to the clause, not to a large
/// array.
const DEFINED_EVIDENCE_ELEMENT_LIMIT: u32 = 4096;

/// The refusal for the first plain memory input whose caller bytes are not
/// all initialized, if any. A recognized byte copy's source is exempt: the
/// copy carries each byte's initialization across, as C allows for the
/// indeterminate bytes of an object representation.
pub(super) fn uninitialized_call_input<'a>(
    memory: &CMemory,
    interface: &CFunctionContractInterface,
    inputs: impl Iterator<Item = &'a CCheckedResourceFact>,
    representation_copy: bool,
    assumptions: &PureFactContext,
) -> Option<String> {
    let requires = interface.resource_requires();
    // A constructor, or a function that constructs its result in place, runs
    // on raw storage: its proof starts with the object unwritten, so the
    // clauses naming that object claim nothing about it.
    let constructed = interface
        .construction_parameter()
        .and_then(|(index, _)| interface.parameters().get(index))
        .map(CParameter::name)
        .or_else(|| {
            (interface.aggregate_return_mode() == CAggregateReturnMode::Construction)
                .then_some(crate::kernel::C_CONTRACT_RESULT_NAME)
        });
    for input in inputs {
        let CResource::Memory(range) = input.fact.resource() else {
            continue;
        };
        let segment = input
            .section_index
            .and_then(|index| requires.get(index))
            .and_then(|spec| spec.term().memory_segment());
        if segment.is_some_and(CMemorySegment::is_uninitialized)
            || (representation_copy && input.fact.is_view())
            || segment
                .zip(constructed)
                .is_some_and(|(segment, constructed)| {
                    root_parameter(&segment.base) == Some(constructed)
                })
        {
            continue;
        }
        if memory_range_is_initialized(
            memory,
            range,
            segment.and_then(CMemorySegment::value_runs),
            assumptions,
        ) {
            continue;
        }
        let clause = match input.clause_position {
            Some((index, total)) => resource_clause_position_note(index, total),
            None => "a memory clause".to_string(),
        };
        return Some(format!(
            "{clause} holds its range as initialized, but the caller has not initialized every byte of it; a callee that writes the range before reading it holds it as `uninitialized(...)`"
        ));
    }
    None
}

/// The parameter a segment's address is computed from.
fn root_parameter(expression: &CExpression) -> Option<&str> {
    match expression {
        CExpression::Variable(name) => Some(name),
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::Subobject { pointer, .. }
        | CExpression::AddressOf(pointer)
        | CExpression::CheckedObjectAddress(pointer)
        | CExpression::Add(pointer, _)
        | CExpression::Subtract(pointer, _) => root_parameter(pointer),
        _ => None,
    }
}

/// Whether every byte of `range` that holds a value is initialized in
/// `memory`; see the module comment.
pub(crate) fn memory_range_is_initialized(
    memory: &CMemory,
    range: &CMemoryRange,
    value_runs: Option<&[(u32, u32)]>,
    assumptions: &PureFactContext,
) -> bool {
    let start = range.start_pointer();
    let tracked = (start.block.is_local_block() && memory.has_block(&start.block))
        || memory.may_read_uninitialized_object(&start, 1)
        || memory.is_uninitialized_heap_address(&start, 1, assumptions);
    if !tracked {
        return true;
    }
    let bytes = if range.wide_bounds().is_some() {
        None
    } else {
        range.byte_footprint().1.as_const()
    };
    let width = range.element_width();
    match (bytes, value_runs) {
        (Some(0), _) => true,
        // Only the bytes that hold values: padding holds nothing to
        // initialize.
        (Some(bytes), Some(runs)) => runs.iter().all(|&(offset, length)| {
            offset.checked_add(length).is_none_or(|end| end > bytes)
                || bytes_are_initialized(
                    memory,
                    &start.offset_by_bytes(offset),
                    length,
                    length,
                    assumptions,
                )
        }),
        (Some(bytes), None) => bytes_are_initialized(memory, &start, bytes, width, assumptions),
        // A length known only at the call: every byte from the start to the
        // end of a constant-size object covers it.
        (None, _) => match (start.offset.as_const(), memory.block_size(&start.block)) {
            (Some(offset), Some(size)) => size
                .as_const()
                .and_then(|size| u32::try_from(i64::from(size) - offset).ok())
                .is_some_and(|rest| {
                    rest == 0 || memory.has_initialized_bytes_under(&start, rest, assumptions)
                }),
            _ => false,
        },
    }
}

/// The bytes written, or each `width`-byte element of them written or
/// `defined` by a fact such as a callee's `ensures defined(p[k])`.
fn bytes_are_initialized(
    memory: &CMemory,
    start: &Pointer,
    bytes: u32,
    width: u32,
    assumptions: &PureFactContext,
) -> bool {
    written(memory, start, bytes, assumptions)
        || elements_are_initialized(memory, start, bytes, width, assumptions)
}

/// The initialization record covers the bytes, or a cell cached at exactly
/// this address does: a cell is evidence its bytes were written.
fn written(memory: &CMemory, start: &Pointer, bytes: u32, assumptions: &PureFactContext) -> bool {
    memory.has_initialized_bytes_under(start, bytes, assumptions)
        || memory
            .known_value(start)
            .is_some_and(|value| value.byte_width() >= bytes)
}

/// Each element written, or `defined` by a fact such as a callee's
/// `ensures defined(p[k])`.
fn elements_are_initialized(
    memory: &CMemory,
    start: &Pointer,
    bytes: u32,
    width: u32,
    assumptions: &PureFactContext,
) -> bool {
    if width == 0 || !bytes.is_multiple_of(width) || bytes / width > DEFINED_EVIDENCE_ELEMENT_LIMIT
    {
        return false;
    }
    (0..bytes / width).all(|index| {
        let element = start.offset_by_bytes(index * width);
        written(memory, &element, width, assumptions)
            || element_types_of_width(width).iter().any(|value_type| {
                assumptions.has_memory_read_defined_evidence(memory, &element, *value_type)
            })
    })
}

/// The scalar types a `defined(p[k])` fact of this element width may name.
fn element_types_of_width(width: u32) -> &'static [CType] {
    match width {
        1 => &[CType::UInt8, CType::Int8],
        2 => &[CType::UInt16, CType::Int16],
        4 => &[CType::Int32, CType::UInt32],
        8 => &[CType::Int64, CType::UInt64],
        _ => &[],
    }
}
