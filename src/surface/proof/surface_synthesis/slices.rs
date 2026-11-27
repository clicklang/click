//! Raising the values of the built-in slice type
//! (`design/rust-slice-values.md`, step 2b-iii-c-ii). A slice raises as the
//! one value that names it where one does: a binder or parameter (`s`), a
//! slice-valued pure application (`f(x)`) or a read of a slice cell; any
//! other slice as its construction, `slice::from_raw_parts(p, n)`. Its
//! components raise as `s.len()` and `s.as_ptr()` of the slice that names
//! them. Each spelling lowers back to the same kernel term: the name to the
//! value it names, `len` and `as_ptr` to the components read in place, and
//! `from_raw_parts` to the wide pointer it builds.

use super::*;

fn slice_call(name: &str, arguments: Vec<SyntaxTerm>) -> SyntaxTerm {
    SyntaxTerm::Call {
        name: name.to_string(),
        arguments,
    }
}

/// The wide pointer `slice` as Surface.
pub(super) fn raise_slice(
    slice: &crate::kernel::Pointer,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let count = slice.len()?;
    let thin = slice.as_ptr();
    if let Some(named) = named_slice(
        thin.address(),
        count,
        slice.program_type(),
        parameter_binding,
        state,
        bound_variables,
    ) {
        return Some(named);
    }
    let data = raise_slice_data(thin.address(), parameter_binding, state, bound_variables)?;
    let count = synthesize_surface_bitvector(count, parameter_binding, state, bound_variables)?;
    Some(slice_call(
        crate::surface::RUST_SLICE_FROM_RAW_PARTS,
        vec![data, count],
    ))
}

/// The slice whose undisplaced data pointer is `address` and whose count is
/// `count`, when one value names both: a slice named by a variable, a
/// slice-valued pure application, or a read of a slice cell.
fn named_slice(
    address: &Address,
    count: &OldMachineTerm,
    slice_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if !matches!(address.offset.view(), OffsetView::Constant(0)) {
        return None;
    }
    match (&address.base, count) {
        (AddressBase::Symbolic(variable), OldMachineTerm::Variable(counted))
            if counted.counted_slice() == Some(*variable) =>
        {
            slice_variable(*variable, parameter_binding, state, bound_variables)
        }
        (
            AddressBase::PureFunctionApplication(application),
            OldMachineTerm::PureApplicationCount(counted),
        ) if application == counted && !application.name().starts_with('$') => {
            synthesize_surface_call(
                application.name(),
                application.arguments(),
                parameter_binding,
                state,
                bound_variables,
            )
        }
        (
            AddressBase::SliceData(load),
            OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount),
        ) if read.load() == load => {
            slice_read(load, slice_type, parameter_binding, state, bound_variables)
        }
        _ => None,
    }
}

/// The slice the variable `variable` names (`design/rust-slice-values.md`,
/// step 2b-iii-a): a proof binder's name, or the parameter whose argument is
/// that slice.
fn slice_variable(
    variable: Variable,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    if let Some(name) =
        folds::binder_name(false, variable).or_else(|| bound_variables.get(&variable).cloned())
    {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            name.into(),
        )));
    }
    if let Some(parameter) = slice_parameter_of(variable, parameter_binding) {
        return Some(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::surface::surface_parameter_binding(parameter.binding_name()),
        )));
    }
    // A slice a call returned, or another value named where it was
    // introduced, is named by its address's routes.
    synthesize_surface_pointer_expression(
        &Address::symbolic(variable),
        parameter_binding,
        state,
        bound_variables,
    )
}

/// The parameter whose argument is the slice `variable` names.
fn slice_parameter_of<'a>(
    variable: Variable,
    parameter_binding: ParameterBinding<'a>,
) -> Option<&'a crate::languages::interface::ImportedParameter> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            crate::instrumentation::record_deterministic_work(1);
            let ProgramExpression::Value(ProgramValue::Pointer(value)) = argument else {
                return None;
            };
            (value.is_wide()
                && value.address().base == AddressBase::Symbolic(variable)
                && matches!(value.address().offset.view(), OffsetView::Constant(0)))
            .then_some(parameter)
        })
}

/// The slice stored in a slice cell, read where `load` reads it, at
/// `slice_type`: the read of that place.
fn slice_read(
    load: &crate::kernel::Load,
    slice_type: ProgramType,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    synthesize_point_read(
        load.point(),
        load.cell(),
        slice_type,
        parameter_binding,
        state,
        bound_variables,
    )
}

/// The count of a slice, `count`, as `s.len()` of the slice that names it:
/// a variable's slice, a slice-valued application, or a slice cell's read.
/// `None` for a term that is no slice's own count.
pub(super) fn raise_slice_count(
    count: &OldMachineTerm,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let slice = match count {
        OldMachineTerm::Variable(counted) => slice_variable(
            counted.counted_slice()?,
            parameter_binding,
            state,
            bound_variables,
        )?,
        OldMachineTerm::PureApplicationCount(application)
            if !application.name().starts_with('$') =>
        {
            synthesize_surface_call(
                application.name(),
                application.arguments(),
                parameter_binding,
                state,
                bound_variables,
            )?
        }
        // The count does not fix the element type; the cell's declaration
        // does, as for a pointer load nested in an address
        // (`design/loads.md`, "Raising").
        OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount) => slice_read(
            read.load(),
            ProgramType::Pointer,
            parameter_binding,
            state,
            bound_variables,
        )?,
        _ => return None,
    };
    Some(slice_call(crate::surface::RUST_SLICE_LEN, vec![slice]))
}

/// A slice's data pointer, `address`, as `s.as_ptr()` of the slice that
/// names it, displaced by its element index, where a slice names its base;
/// any other thin pointer by its address's routes.
pub(super) fn raise_slice_data(
    address: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    slice_data_pointer(address, parameter_binding, state, bound_variables).or_else(|| {
        synthesize_surface_pointer_expression(address, parameter_binding, state, bound_variables)
    })
}

/// The thin pointer `address` as `s.as_ptr()`, or `s.as_ptr() + k`, when
/// its base is the data pointer of a slice `s` that names it: a slice read,
/// a slice-valued pure call, a slice binder or a slice parameter. `None` for
/// any other base.
pub(super) fn slice_data_pointer(
    address: &Address,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    bound_variables: &BTreeMap<Variable, SurfaceBinder>,
) -> Option<SyntaxTerm> {
    let (slice, element_width) = match &address.base {
        AddressBase::SliceData(load) => {
            let read = slice_read(
                load,
                ProgramType::Pointer,
                parameter_binding,
                state,
                bound_variables,
            )?;
            let width = spelled_slice_element_width(&read)?;
            (read, width)
        }
        // A slice-valued pure call is the slice; its data pointer is based
        // on the application (`design/rust-slice-values.md`, step
        // 2b-iii-b-ii).
        AddressBase::PureFunctionApplication(application)
            if !application.name().starts_with('$') =>
        {
            let element = crate::surface::diagnostics::slice_result_element(application.name())?;
            (
                synthesize_surface_call(
                    application.name(),
                    application.arguments(),
                    parameter_binding,
                    state,
                    bound_variables,
                )?,
                element.thin_pointer_type().pointee_type()?.byte_width(),
            )
        }
        // A match arm's slice binder.
        AddressBase::Symbolic(variable)
            if let Some(element) = folds::slice_binder_element(*variable)
                && let Some(name) = folds::binder_name(false, *variable) =>
        {
            (
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name.into())),
                element.thin_pointer_type().pointee_type()?.byte_width(),
            )
        }
        AddressBase::Symbolic(variable) => {
            let parameter = slice_parameter_of(*variable, parameter_binding)?;
            let crate::languages::interface::InterfaceType::Slice(element) =
                parameter.interface_type()
            else {
                return None;
            };
            (
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    crate::surface::surface_parameter_binding(parameter.binding_name()),
                )),
                element.thin_pointer_type().pointee_type()?.byte_width(),
            )
        }
        _ => return None,
    };
    let data = slice_call(crate::surface::RUST_SLICE_AS_PTR, vec![slice]);
    let origin = address.with_offset(crate::kernel::AddressOffset::constant(0));
    let index = synthesis_element_index(address, &origin, element_width)?;
    if pointer_indices::literal(index.operand_view()) == Some(OldMachineTerm::constant(0)) {
        return Some(data);
    }
    let index = pointer_indices::raise(
        index.operand_view(),
        parameter_binding,
        state,
        bound_variables,
    )?;
    Some(SyntaxTerm::Add(Box::new(data), Box::new(index)))
}

/// The element width of the slice a spelled read reads, from its lowered
/// load's type.
fn spelled_slice_element_width(read: &SyntaxTerm) -> Option<u32> {
    let ProgramType::SlicePointer(element) = spelled_load_type(read)? else {
        return None;
    };
    Some(element.thin_pointer_type().pointee_type()?.byte_width())
}
