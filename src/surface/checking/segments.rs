use super::*;
use crate::kernel::binary_term;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct EvaluatedContractSegment {
    pub(in crate::surface) source: ContractSegment,
    pub(in crate::surface) base: Pointer,
    pub(in crate::surface) start: MachineTerm,
    pub(in crate::surface) end: MachineTerm,
    pub(in crate::surface) element_width: u32,
}

pub(in crate::surface) fn evaluate_requirement_segment(
    parameter_binding: ParameterBinding<'_>,
    entry_state: &ExecutionState,
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "requirement segments are entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    // A segment reads only the parameters it names.
    let parameter_values = parameter_values_named(
        parameter_binding,
        &crate::surface::lowering::contract_segment_referenced_names(segment),
    )
    .map_err(|error| error.message)?;
    let array_refs =
        array_refs_for_values(parameter_binding, &parameter_values, entry_state.memory());
    evaluate_segment_bounds(
        segment,
        &PureFactContext::new(),
        ContractEnvironment::new(&parameter_values, &array_refs),
        entry_state,
        contract_segment_element_width(parameter_binding.parameters, segment),
    )
}

/// A requirement segment's base pointer alone, for a segment whose bounds
/// need not be `int32`.
pub(in crate::surface) fn evaluate_requirement_segment_base(
    parameter_binding: ParameterBinding<'_>,
    entry_state: &ExecutionState,
    segment: &ContractSegment,
) -> Result<Pointer, String> {
    let parameter_values = parameter_values_named(
        parameter_binding,
        &crate::surface::lowering::contract_segment_referenced_names(segment),
    )
    .map_err(|error| error.message)?;
    let array_refs =
        array_refs_for_values(parameter_binding, &parameter_values, entry_state.memory());
    let ProgramValue::Pointer(base) = crate::surface::proof::evaluate_c_fragment_through_kernel(
        &segment.base,
        &PureFactContext::new(),
        ContractEnvironment::new(&parameter_values, &array_refs),
        entry_state,
        None,
    )?
    else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    Ok(base.into_pointer())
}

/// A segment's base, start, and end, each evaluated by the kernel at
/// `state` as the C fragment it is.
fn evaluate_segment_bounds(
    segment: &ContractSegment,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    state: &ExecutionState,
    element_width: u32,
) -> Result<EvaluatedContractSegment, String> {
    let evaluate = |expression: &ProgramExpression| {
        crate::surface::proof::evaluate_c_fragment_through_kernel(
            expression,
            assumptions,
            contract_environment,
            state,
            None,
        )
    };
    let ProgramValue::Pointer(base) = evaluate(&segment.base)? else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let ProgramValue::Int32(start) = evaluate(&segment.start)? else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let ProgramValue::Int32(end) = evaluate(&segment.end)? else {
        return Err("segment end did not evaluate to int32".to_string());
    };
    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base: base.into_pointer(),
        start,
        end,
        element_width,
    })
}

pub(in crate::surface) fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(index) = pointer_element_index_from_base_with_width(
        pointer,
        &segment.base,
        segment.element_width,
        assumptions,
    ) else {
        return false;
    };
    crate::kernel::search::ProofSearch::proves(
        assumptions,
        &Proposition::ConditionIs(
            signed_less_equal(segment.start.clone(), index.clone()),
            true,
        ),
    ) && crate::kernel::search::ProofSearch::proves(
        assumptions,
        &Proposition::ConditionIs(signed_less_than(index, segment.end.clone()), true),
    )
}
#[cfg(test)]
pub(in crate::surface) fn pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    assumptions: &PureFactContext,
) -> Option<MachineTerm> {
    pointer_element_index_from_base_with_width(pointer, base, 4, assumptions)
}

fn pointer_element_index_from_base_with_width(
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<MachineTerm> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset
        || pointer_offsets_equal_for_effect(&pointer.offset, &base.offset, assumptions)
    {
        return Some(MachineTerm::constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return element_index_from_pointer_offset(&pointer.offset, element_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right)
            if left.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(left, &base.offset, assumptions) =>
        {
            element_index_from_pointer_offset(right, element_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(right, &base.offset, assumptions) =>
        {
            element_index_from_pointer_offset(left, element_width)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                element_index_from_pointer_offset(&pointer.offset, element_width),
                element_index_from_pointer_offset(&base.offset, element_width),
            ) {
                Some(bitvector_index_relative_to_base(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

fn pointer_offsets_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    c_pointer_offsets_proven_equal_for_effect(left, right, assumptions)
}

fn element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    element_width: u32,
) -> Option<MachineTerm> {
    if element_width == 0 {
        return None;
    }
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % i64::from(element_width) == 0 => {
            let index = offset / i64::from(element_width);
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(MachineTerm::constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(value.structural_value().clone())
        }
        PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } if *byte_width == i64::from(element_width) => Some(value.structural_value().clone()),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            element_index_from_pointer_offset(right, element_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            element_index_from_pointer_offset(left, element_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            element_index_from_pointer_offset(left, element_width)?,
            element_index_from_pointer_offset(right, element_width)?,
        )),
        _ => None,
    }
}
fn bitvector_index_relative_to_base(
    pointer_index: MachineTerm,
    base_index: MachineTerm,
) -> MachineTerm {
    if pointer_index == base_index {
        return MachineTerm::constant(0);
    }
    if let binary_term!(Int32, Add, left, right) = &pointer_index {
        if left.as_ref() == &base_index {
            return right.as_ref().clone();
        }
        if right.as_ref() == &base_index {
            return left.as_ref().clone();
        }
    }
    bitvector32_subtract(pointer_index, base_index)
}
