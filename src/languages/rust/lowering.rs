use super::schema::{Expression as E, Function, Record, RustExport, Statement as S, Type};
#[cfg(test)]
mod array_reference_tests;
mod arrays;
mod chunks;
mod enumerate;
#[cfg(test)]
mod move_regressions;
mod moves;
#[cfg(test)]
mod owned_parameter_regressions;
mod ranges;
#[cfg(test)]
mod record_pointer_fields_tests;
mod scalar_leases;
mod shared_arrays;
use crate::kernel::*;
use crate::languages::c::syntax::LongRank;
use crate::languages::interface::{
    CallbackInterface, CallbackParameter, ImportedFunction, ImportedParameter, InterfaceType,
    RecordLayout,
};
use std::collections::{BTreeMap, BTreeSet};

// Rust reference lowering changes the access type without introducing C's
// authored character/void cast escape. Preserve the complete pointer domain.
fn reference_view(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
    pointee_constant: bool,
) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: IntegerCastMode::PointerCoercion,
        pointee_struct: None,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: false,
    }
}

pub(crate) type LoweredRust = (Vec<ImportedFunction>, BTreeMap<String, RecordLayout>);

thread_local! {
    /// Whether the export being lowered reads a slice iterator through its
    /// Click library contract ([`RustExport::library_iterators`]), set for
    /// one lowering with the enum types.
    static LIBRARY_ITERATORS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The kernel types of the crate enums being lowered, by name. One
    /// lowering runs on one thread and sets them for its duration
    /// ([`EnumTypes::enter`]), so a type is found from its name alone.
    static ENUM_TYPES: std::cell::RefCell<BTreeMap<String, TypeParameterName>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// The crate's enums for the duration of one lowering.
struct EnumTypes;

impl EnumTypes {
    fn enter(export: &RustExport) -> Result<Self, String> {
        // Each enum is known as soon as it is declared, and the guard clears
        // them all if a later one is refused.
        ENUM_TYPES.with(|known| known.borrow_mut().clear());
        let guard = Self;
        // Crate enums first: a library enum instance may hold one,
        // `Result<u32, ParseError>`.
        let (crate_enums, instances): (Vec<_>, Vec<_>) = export
            .enums
            .iter()
            .partition(|declared| declared.generic.is_none());
        for declared in crate_enums.into_iter().chain(instances) {
            // A library enum instance's payload of a crate enum is that enum
            // itself, `Result<u32, ParseError>`'s error a `ParseError`, whose
            // variants the instance's schemas carry.
            let mut nested = BTreeMap::new();
            let mut payload_type = |t: &Type| -> Result<Option<AlgebraicValueType>, String> {
                let Type::Enum { name } = t else {
                    return Ok(None);
                };
                if declared.generic.is_none() {
                    return Ok(None);
                }
                let enum_type = EnumTypes::get(name)?.algebraic_type();
                let value_type = enum_type.value_type();
                nested.insert(value_type.clone(), enum_type.variants.clone());
                Ok(Some(value_type))
            };
            let variants: std::sync::Arc<[AlgebraicVariantType]> = declared
                .variants
                .iter()
                .map(|variant| {
                    Ok(AlgebraicVariantType {
                        name: variant.name.clone(),
                        fields: variant
                            .fields
                            .iter()
                            .map(|field| {
                                if let Some(nested) = payload_type(field)? {
                                    return Ok(nested);
                                }
                                let interface_type = scalar_type(field)?;
                                // The library's `Option` of a shared
                                // reference, which a slice iterator's
                                // `next()` returns, holds that reference.
                                // So does the library's `Slice`, a shared
                                // slice's data and length.
                                let reference_payload =
                                    matches!(declared.generic.as_deref(), Some("Option" | "Slice"))
                                        && matches!(field, Type::Reference { mutable: false, .. });
                                if interface_type == InterfaceType::Void
                                    || (interface_type.is_pointer() && !reference_payload)
                                {
                                    return Err(
                                        "Rust enum fields must be integers or booleans".to_string()
                                    );
                                }
                                Ok(AlgebraicValueType::Program(interface_type.to_kernel_type()))
                            })
                            .collect::<Result<_, String>>()?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?
                .into();
            // An instance of a library enum is that `spec enum` at its
            // arguments: `Option<u32>` is `Option` at `u32`.
            let spec_name = declared.generic.as_ref().unwrap_or(&declared.name);
            let arguments = declared
                .arguments
                .iter()
                .map(|argument| {
                    if let Some(nested) = payload_type(argument)? {
                        return Ok(nested);
                    }
                    Ok(AlgebraicValueType::Program(
                        scalar_type(argument)?.to_kernel_type(),
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let nominal = AlgebraicValueType::Algebraic {
                name: spec_name.clone(),
                arguments: arguments.clone(),
            };
            nested.insert(nominal, variants.clone());
            let algebraic_type = AlgebraicType {
                rigid: false,
                name: spec_name.clone(),
                arguments,
                variants: variants.clone(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(nested)),
            };
            let duplicate = ENUM_TYPES.with(|known| {
                known
                    .borrow_mut()
                    .insert(
                        declared.name.clone(),
                        TypeParameterName::of(&algebraic_type),
                    )
                    .is_some()
            });
            if duplicate {
                return Err("duplicate Rust enum".into());
            }
        }
        Ok(guard)
    }

    fn get(name: &str) -> Result<TypeParameterName, String> {
        ENUM_TYPES
            .with(|known| known.borrow().get(name).copied())
            .ok_or_else(|| format!("unknown Rust enum `{name}`"))
    }
}

impl Drop for EnumTypes {
    fn drop(&mut self) {
        ENUM_TYPES.with(|known| known.borrow_mut().clear());
    }
}

/// The C type of field `index` of variant `variant` of enum `name`, when
/// that field is itself an enum: `Result<u32, ParseError>`'s `Err` field.
fn nested_enum_field_type(
    name: &str,
    variant: &str,
    index: usize,
) -> Result<Option<InterfaceType>, String> {
    let enum_type = EnumTypes::get(name)?.algebraic_type();
    let Some(AlgebraicValueType::Algebraic { name: field, .. }) = enum_type
        .variants
        .iter()
        .find(|declared| declared.name == variant)
        .and_then(|declared| declared.fields.get(index))
    else {
        return Ok(None);
    };
    Ok(Some(InterfaceType::Parameter(EnumTypes::get(field)?)))
}

fn scalar_type(t: &Type) -> Result<InterfaceType, String> {
    match t {
        Type::Enum { name } => Ok(InterfaceType::Parameter(EnumTypes::get(name)?)),
        Type::I8 => Ok(InterfaceType::Int8),
        Type::I16 => Ok(InterfaceType::Int16),
        Type::I32 => Ok(InterfaceType::Int32),
        Type::I64 | Type::Isize => Ok(InterfaceType::Int64(LongRank::Long)),
        Type::U8 => Ok(InterfaceType::UInt8),
        Type::U16 => Ok(InterfaceType::UInt16),
        Type::U32 => Ok(InterfaceType::UInt32),
        Type::U64 | Type::Usize => Ok(InterfaceType::UInt64(LongRank::Long)),
        Type::Bool => Ok(InterfaceType::Bool),
        Type::Unit => Ok(InterfaceType::Void),
        Type::Parameter { name } => Ok(InterfaceType::Parameter(
            crate::kernel::TypeParameterName::intern(name),
        )),
        Type::Vec { element } => Ok(InterfaceType::Parameter(vec_type(element)?)),
        // In the library-iterator model, the iterator is a value of the
        // library's `ChunksExact<uint8>`.
        Type::ChunkIterator => Ok(InterfaceType::Parameter(chunks_exact_type())),
        // A slice iterator passed to its library operations is a value of
        // the library's `SliceIter`.
        Type::SharedArrayIterator { element } => {
            Ok(InterfaceType::Parameter(slice_iter_type(element)?))
        }
        // A box of a crate struct is its address, as a struct reference is.
        Type::Box { .. } | Type::OptionBox { .. } => Ok(InterfaceType::Int32Pointer),
        Type::Reference { pointee, .. } => match pointee.as_ref() {
            // A reference to a value of unknown type is opaque as a struct
            // reference is: nothing is read through it without its fields.
            Type::I32 | Type::Record { .. } | Type::TraitObject => Ok(InterfaceType::Int32Pointer),
            Type::U8 => Ok(InterfaceType::UInt8Pointer),
            Type::U16 => Ok(InterfaceType::UInt16Pointer),
            Type::U32 => Ok(InterfaceType::UInt32Pointer),
            Type::I8 => Ok(InterfaceType::Int8Pointer),
            Type::I16 => Ok(InterfaceType::Int16Pointer),
            Type::I64 | Type::Isize => Ok(InterfaceType::Int64Pointer(LongRank::Long)),
            Type::U64 | Type::Usize => Ok(InterfaceType::UInt64Pointer(LongRank::Long)),
            Type::Parameter { name } => Ok(InterfaceType::ParameterPointer(
                crate::kernel::TypeParameterName::intern(name),
            )),
            // An enum value is a spec value, as a type parameter's is.
            Type::Enum { name } => Ok(InterfaceType::ParameterPointer(EnumTypes::get(name)?)),
            Type::Vec { element } => Ok(InterfaceType::ParameterPointer(vec_type(element)?)),
            Type::SharedArrayIterator { element } => {
                Ok(InterfaceType::ParameterPointer(slice_iter_type(element)?))
            }
            Type::ChunkIterator => Ok(InterfaceType::ParameterPointer(chunks_exact_type())),
            Type::Array { element, .. } => match element.as_ref() {
                Type::I32 => Ok(InterfaceType::Int32Pointer),
                Type::U8 => Ok(InterfaceType::UInt8Pointer),
                Type::U32 => Ok(InterfaceType::UInt32Pointer),
                _ => Err("fixed arrays require i32, u8 or u32 elements".into()),
            },
            _ => Err("Rust reference pointee outside scalar/reference lowering".into()),
        },
        Type::Array { .. } => Err("Rust array values require whole-array lowering".into()),
        Type::FnPointer { .. } => Ok(fn_pointer_signature(t)?.pointer_type()),
        _ => Err("Rust value type outside direct scalar/reference lowering".into()),
    }
}
/// The type of a `Vec<element>` value: the library's primitive `Vec` at
/// `element`, which the kernel reads as a rigid type of its own.
fn vec_type(element: &Type) -> Result<crate::kernel::TypeParameterName, String> {
    let element = scalar_type(element)?.to_kernel_type();
    Ok(crate::kernel::TypeParameterName::of(
        &crate::surface::primitive_instance_type("Vec", &[AlgebraicValueType::Program(element)]),
    ))
}
/// Whether this lowering reads a slice iterator through its library contract.
fn library_iterators() -> bool {
    LIBRARY_ITERATORS.with(std::cell::Cell::get)
}
/// The type of a slice iterator over `element`: the library's primitive
/// `SliceIter` at the element's type.
fn slice_iter_type(element: &Type) -> Result<crate::kernel::TypeParameterName, String> {
    let element = scalar_type(element)?.to_kernel_type();
    Ok(crate::kernel::TypeParameterName::of(
        &crate::surface::primitive_instance_type(
            "SliceIter",
            &[AlgebraicValueType::Program(element)],
        ),
    ))
}
/// The type of a `chunks_exact` iterator over bytes: the library's primitive
/// `ChunksExact` at `uint8`.
fn chunks_exact_type() -> crate::kernel::TypeParameterName {
    crate::kernel::TypeParameterName::of(&crate::surface::primitive_instance_type(
        "ChunksExact",
        &[AlgebraicValueType::Program(ProgramType::UInt8)],
    ))
}
/// A function-pointer type's signature, as a sidecar's `fn(i32) -> i32`
/// parameter type spells it.
fn fn_pointer_signature(t: &Type) -> Result<CallbackInterface, String> {
    let Type::FnPointer { parameters, result } = t else {
        return Err("Rust function-pointer signature requires a function-pointer type".into());
    };
    let parameters = parameters
        .iter()
        .map(|parameter| {
            let interface_type = scalar_type(parameter)?;
            if interface_type == InterfaceType::Void || interface_type.is_pointer() {
                return Err("Rust function-pointer parameters must be scalars".to_string());
            }
            Ok(CallbackParameter::new(interface_type, None, false))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let result = scalar_type(result)?;
    if result.is_pointer() {
        return Err("Rust function-pointer results must be scalars or unit".into());
    }
    Ok(CallbackInterface::new(result, None, parameters, false))
}
// Embedded arrays retain one ABI field and their concrete extent. Never
// flatten a field into one layout entry per element.
fn record_field_type(t: &Type) -> Result<InterfaceType, String> {
    let Type::Array { element, length } = t else {
        return scalar_type(t);
    };
    let element = scalar_type(element)?.to_kernel_type();
    let length = arrays::array_length(element, *length)?;
    Ok(match element {
        ProgramType::Int32 => InterfaceType::Int32Array(length),
        ProgramType::UInt8 => InterfaceType::UInt8Array(length),
        ProgramType::UInt32 => InterfaceType::UInt32Array(length),
        _ => unreachable!(),
    })
}
fn array_field_parts(t: ProgramType) -> Option<(ProgramType, u32)> {
    match t {
        ProgramType::Int32Array(n) => Some((ProgramType::Int32, n)),
        ProgramType::UInt8Array(n) => Some((ProgramType::UInt8, n)),
        ProgramType::UInt32Array(n) => Some((ProgramType::UInt32, n)),
        _ => None,
    }
}
// Rust integer `as` uses the same explicit modulo policy as C++20.
/// The Rust integer type a slice or array element of C type `element` is.
fn indexed_element_type(element: ProgramType) -> Option<Type> {
    Some(match element {
        ProgramType::UInt8 => Type::U8,
        ProgramType::UInt16 => Type::U16,
        ProgramType::UInt32 => Type::U32,
        ProgramType::UInt64 => Type::U64,
        ProgramType::Int8 => Type::I8,
        ProgramType::Int16 => Type::I16,
        ProgramType::Int32 => Type::I32,
        ProgramType::Int64 => Type::I64,
        _ => return None,
    })
}
/// A branch's or loop's condition: a `bool` value written as a condition is
/// the comparison it tests, which the branch splits on (Stage 5, D5).
fn branch_condition(condition: ProgramExpression) -> ProgramExpression {
    match condition {
        ProgramExpression::Cast {
            expression,
            integer_mode: IntegerCastMode::BoolValue,
            ..
        } => *expression,
        condition => condition,
    }
}

fn rust_scalar_cast(value: ProgramExpression, target: ProgramType) -> ProgramExpression {
    if crate::kernel::MachineIntegerType::from_program_type(target).is_some() {
        crate::kernel::program_expression::integer_cast_modulo(value, target)
    } else if target.is_pointer() {
        reference_view(value, target, false, false)
    } else {
        crate::kernel::program_expression::cast(value, target)
    }
}
/// Rust `!value` on an integer of type `target`: at 8 or 16 bits the native
/// complement of that type (decision G4), otherwise the complement of the
/// value's word converted modularly to `target`.
fn rust_bitwise_not(value: ProgramExpression, target: ProgramType) -> ProgramExpression {
    if matches!(
        target,
        ProgramType::Int8 | ProgramType::UInt8 | ProgramType::Int16 | ProgramType::UInt16
    ) {
        crate::kernel::program_expression::narrow_arithmetic(
            crate::kernel::program_expression::bitwise_not(value),
            target,
        )
    } else {
        rust_scalar_cast(
            crate::kernel::program_expression::bitwise_not(value),
            target,
        )
    }
}
fn integer_from(
    value: ProgramExpression,
    source: &Type,
    target: &Type,
) -> Result<ProgramExpression, String> {
    if !source.converts_losslessly_to(target) {
        return Err("integer From requires a supported lossless conversion".into());
    }
    Ok(crate::kernel::program_expression::cast(
        value,
        scalar_type(target)?.to_kernel_type(),
    ))
}
pub(crate) fn lower(export: &RustExport) -> Result<LoweredRust, String> {
    lower_with_identity(export, None)
}
pub(crate) fn lower_with_identity(
    export: &RustExport,
    identity: Option<&str>,
) -> Result<LoweredRust, String> {
    // Enum fields are scalars, so their types need no other enum's.
    let _enums = EnumTypes::enter(export)?;
    LIBRARY_ITERATORS.with(|library| library.set(export.library_iterators));
    let mut layouts = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for record in &export.records {
        let mut layout_fields = record
            .fields
            .iter()
            .map(|f| {
                Ok((
                    f.name.clone(),
                    record_field_type(&f.value_type)?,
                    match &f.value_type {
                        Type::Reference { pointee, .. }
                        | Type::Box { pointee }
                        | Type::OptionBox { pointee } => match pointee.as_ref() {
                            Type::Record { name } => Some(name.clone()),
                            _ => None,
                        },
                        _ => None,
                    },
                    f.offset,
                    record_field_type(&f.value_type)?
                        .to_kernel_type()
                        .byte_width(),
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        // Rust may reorder fields; declaration order still selects constructor
        // operands, while layout validation consumes physical offset order.
        layout_fields.sort_by_key(|f| f.3);
        // Pointer fields keep their nominal pointee for chained field reads.
        // They do not embed its layout, so recursive records need no traversal.
        let layout = RecordLayout::from_explicit_fields_with_structs(
            layout_fields,
            record.size,
            record.alignment,
            &BTreeMap::new(),
        )?;
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err("duplicate Rust record".into());
        }
        for f in &record.fields {
            if fields
                .insert(
                    (record.name.as_str(), f.name.as_str()),
                    (f.offset, record_field_type(&f.value_type)?.to_kernel_type()),
                )
                .is_some()
            {
                return Err("duplicate Rust field".into());
            }
        }
    }
    let record_index = export
        .records
        .iter()
        .map(|r| (r.name.as_str(), r))
        .collect::<BTreeMap<_, _>>();
    let function_index = export
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect::<BTreeMap<_, _>>();
    let mut names = BTreeSet::new();
    let mut functions = Vec::new();
    for f in &export.functions {
        if !names.insert(f.name.clone()) {
            return Err("duplicate Rust function name".into());
        }
        functions.push(
            lower_function(
                export,
                identity,
                f,
                &fields,
                &layouts,
                &record_index,
                &function_index,
            )
            .map_err(|error| located(&export.logical_source, f, error))?,
        );
    }
    Ok((functions, layouts))
}
/// `error`, refusing to lower `f`, with the function's source location
/// unless it already names one.
fn located(source: &str, f: &Function, error: String) -> String {
    if error.starts_with(&format!("{source}:")) {
        return error;
    }
    let name = super::names::rust_display_name(&f.name).unwrap_or_else(|| f.name.clone());
    format!("{source}:{} in {name}: {error}", f.span.line)
}

fn lower_function(
    export: &RustExport,
    identity: Option<&str>,
    f: &Function,
    fields: &BTreeMap<(&str, &str), (u32, ProgramType)>,
    layouts: &BTreeMap<String, RecordLayout>,
    records: &BTreeMap<&str, &Record>,
    functions: &BTreeMap<&str, &Function>,
) -> Result<ImportedFunction, String> {
    if !(f.return_type.is_scalar()
        || matches!(
            f.return_type,
            Type::Unit
                | Type::Record { .. }
                | Type::Enum { .. }
                | Type::Parameter { .. }
                | Type::Vec { .. }
                | Type::Box { .. }
                | Type::OptionBox { .. }
        )
        // The library-iterator model's own external functions return the
        // iterator value, and a chunk's or the remainder's data pointer.
        || f.core_method.as_deref().is_some_and(|method| {
            method.starts_with(super::standard_library::CHUNKS_EXACT)
                || method.starts_with(super::standard_library::SLICE_ITER)
                || method.starts_with(super::standard_library::SLICE_VALUE)
        }))
    {
        return Err("Rust reference/aggregate returns are not supported".into());
    }
    let return_layout = match &f.return_type {
        Type::Record { name } => Some((
            name,
            layouts.get(name).ok_or("missing return record layout")?,
        )),
        _ => None,
    };
    let return_type = if return_layout.is_some() {
        InterfaceType::UInt8Pointer
    } else {
        scalar_type(&f.return_type)?
    };
    let mut parameters = Vec::new();
    let mut kernel_parameters = Vec::new();
    let mut locals = BTreeSet::new();
    let mut slices = BTreeMap::new();
    let mut shared_scalar_slices = BTreeMap::new();
    let mut arrays = BTreeMap::new();
    let mut references = BTreeMap::new();
    let parameter_names: BTreeSet<_> = f
        .parameters
        .iter()
        .map(|p| {
            crate::instrumentation::record_deterministic_work(1);
            p.name.as_str()
        })
        .collect();
    for p in &f.parameters {
        crate::instrumentation::record_deterministic_work(1);
        if matches!(p.value_type, Type::Array { .. }) {
            return Err("by-value Rust arrays as parameters are not supported".into());
        }
        if !locals.insert(p.name.clone()) {
            return Err("duplicate Rust parameter".into());
        }
        if let Type::Record { name } = &p.value_type {
            // A generic function's instance takes the record as the
            // generic function, whose MIR is checked, does.
            if f.mir.is_none() && f.instance_of.is_none() {
                return Err("owned record parameters require compiler MIR".into());
            }
            let layout = layouts.get(name).ok_or("missing parameter record layout")?;
            let parameter =
                ImportedParameter::new(InterfaceType::UInt8Pointer, p.name.clone(), None)
                    .with_struct_value(name.clone(), layout.clone());
            kernel_parameters.push(parameter.to_kernel_parameter());
            parameters.push(parameter);
            continue;
        }
        if let Type::ByteSlice { mutable } = &p.value_type {
            let length = format!("{}_len", p.name);
            if parameter_names.contains(length.as_str()) || !locals.insert(length.clone()) {
                return Err(format!(
                    "Rust slice length parameter `{length}` collides with a parameter"
                ));
            }
            slices.insert(p.name.clone(), (length.clone(), !mutable));
            parameters.push(
                ImportedParameter::new(InterfaceType::UInt8Pointer, p.name.clone(), None)
                    .with_pointee_constant(!mutable)
                    .with_slice_length_parameter(1),
            );
            parameters.push(ImportedParameter::new(
                InterfaceType::UInt64(LongRank::Long),
                length.clone(),
                None,
            ));
            kernel_parameters.push(
                program_parameter(&p.name, ProgramType::UInt8Pointer)
                    .with_pointee_constant(!mutable)
                    .with_slice_length_parameter(1),
            );
            kernel_parameters.push(program_parameter(length, ProgramType::UInt64));
            continue;
        }
        if let Type::ScalarSlice { element, mutable } = &p.value_type {
            if !element.is_integer() {
                return Err("scalar slice parameters require integer elements".into());
            }
            let length = format!("{}_len", p.name);
            if parameter_names.contains(length.as_str()) || !locals.insert(length.clone()) {
                return Err(format!(
                    "Rust slice length parameter `{length}` collides with a parameter"
                ));
            }
            let pointer = scalar_type(&Type::Reference {
                mutable: *mutable,
                pointee: element.clone(),
            })?;
            shared_scalar_slices.insert(
                p.name.clone(),
                (length.clone(), scalar_type(element)?.to_kernel_type()),
            );
            parameters.push(
                ImportedParameter::new(pointer, p.name.clone(), None)
                    .with_pointee_constant(!mutable)
                    .with_slice_length_parameter(1),
            );
            parameters.push(ImportedParameter::new(
                InterfaceType::UInt64(LongRank::Long),
                length.clone(),
                None,
            ));
            kernel_parameters.push(
                program_parameter(&p.name, pointer.to_kernel_type())
                    .with_pointee_constant(!mutable)
                    .with_slice_length_parameter(1),
            );
            kernel_parameters.push(program_parameter(length, ProgramType::UInt64));
            continue;
        }
        if let Type::Reference { mutable, .. } = &p.value_type {
            references.insert(p.name.clone(), !mutable);
        }
        if let Type::FnPointer { .. } = &p.value_type {
            let signature = fn_pointer_signature(&p.value_type)?;
            kernel_parameters.push(program_parameter(
                &p.name,
                signature.pointer_type().to_kernel_type(),
            ));
            parameters.push(ImportedParameter::function_pointer(
                p.name.clone(),
                signature,
            ));
            continue;
        }
        let interface_type = scalar_type(&p.value_type)?;
        if let Type::Reference { mutable, pointee } = &p.value_type
            && let Type::Array { element, length } = pointee.as_ref()
        {
            let element = scalar_type(element)?.to_kernel_type();
            if *length > i32::MAX as u64 / u64::from(element.byte_width()) {
                return Err("fixed array storage exceeds the signed-word memory model".into());
            }
            arrays.insert(p.name.clone(), (*length, element, !mutable));
        }
        if interface_type == InterfaceType::Void {
            return Err("unit parameters outside Rust slice".into());
        }
        let (tag, constant) = match &p.value_type {
            Type::Reference { mutable, pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                !mutable,
            ),
            // A box is the address of the struct it owns.
            Type::Box { pointee } | Type::OptionBox { pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                false,
            ),
            _ => (None, false),
        };
        let mut parameter = ImportedParameter::new(interface_type, p.name.clone(), tag.clone())
            .with_pointee_constant(constant);
        // The record's layout is what seeds a whole-record `owns *x` at its
        // fields' widths, so a 64-bit field reads as one cell.
        if let Some(layout) = tag.as_ref().and_then(|name| layouts.get(name)) {
            parameter = parameter.with_pointee_struct_layout(tag.clone().unwrap(), layout.clone());
        }
        let mut kernel_parameter = program_parameter(&p.name, interface_type.to_kernel_type())
            .with_pointee_constant(constant);
        if let Some((length, element, _)) = arrays.get(&p.name) {
            let bytes = u32::try_from(*length * u64::from(element.byte_width()))
                .expect("validated fixed array extent");
            parameter = parameter.with_fixed_reference_extent(bytes);
            kernel_parameter = kernel_parameter.with_fixed_reference_extent(bytes);
        }
        parameters.push(parameter);
        kernel_parameters.push(kernel_parameter);
    }
    // A declaration in an `extern` block has no body to execute: its calls
    // are checked against the sidecar's `extern fn` contract.
    if f.external {
        if f.mir.is_some() || !f.body.is_empty() {
            return Err("Rust extern function must not carry a body".into());
        }
        // A core method the Click library states is an instance of its
        // library generic function.
        let instance_of = f
            .instance_of
            .clone()
            .or_else(|| super::standard_library::library_generic(f));
        let generic = instance_of.is_some();
        let mut declaration = ImportedFunction::external(return_type, f.name.clone(), parameters)
            .with_generic_instance(instance_of);
        if let Some((name, layout)) = return_layout {
            declaration = declaration.with_struct_return(name.clone(), layout.clone());
        }
        // A generic function's instance names its parameters as the generic
        // function does.
        return Ok(if generic {
            declaration
        } else {
            declaration.with_positional_parameters()
        });
    }
    let mut cx = Context {
        shared_array_iterators: BTreeMap::new(),
        library_slice_iterators: BTreeMap::new(),
        library_slice_options: BTreeMap::new(),
        library_next_options: BTreeMap::new(),
        library_chunk_built: BTreeSet::new(),
        ranges: BTreeMap::new(),
        enumerated: BTreeSet::new(),
        shared_array_options: BTreeMap::new(),
        shared_scalar_slices,
        mir_chunk_iterators: BTreeSet::new(),
        chunk_options: BTreeSet::new(),
        local_arrays: BTreeSet::new(),
        owned_locals: BTreeSet::new(),
        addressable_locals: BTreeSet::new(),
        memory_values: BTreeMap::new(),
        slices,
        arrays,
        references,
        source: &export.logical_source,
        function: &f.name,
        fields,
        next_load: 0,
        import_identity: identity.map(std::sync::Arc::from),
        mir_point: None,
        mir_nodes: BTreeMap::new(),
        next_temporary: 0,
        loop_iterators: Vec::new(),
        locals,
        return_type,
        layouts,
        records,
        functions,
    };
    let body = match &f.mir {
        Some(mir) if f.body.is_empty() => moves::lower(&mut cx, f, mir)?,
        Some(_) => return Err("Rust function must select exactly one body representation".into()),
        None => cx.body(&f.body)?,
    };
    let loop_iterators = std::mem::take(&mut cx.loop_iterators);
    let mut kernel = program_function(
        return_type.to_kernel_type(),
        &f.name,
        kernel_parameters,
        body,
    );
    if let Some((_, layout)) = return_layout {
        kernel = kernel.with_return_aggregate_layout(layout.to_kernel_aggregate_layout());
    }
    let local_records = f
        .mir
        .as_ref()
        .map(|mir| {
            mir.locals
                .iter()
                .filter_map(|local| match &local.value_type {
                    Type::Record { name } => Some((local.name.clone(), name.clone())),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    let mut lowered = ImportedFunction::external(return_type, f.name.clone(), parameters)
        .with_local_struct_values(local_records)
        .with_prelowered_kernel_function(kernel)
        .with_closure_captures(f.captures)
        .with_trait_interface(f.implements.clone())
        .with_loop_iterators(loop_iterators);
    if let Some((name, layout)) = return_layout {
        lowered = lowered.with_struct_return(name.clone(), layout.clone());
    }
    Ok(lowered)
}
struct Context<'a> {
    shared_array_iterators: BTreeMap<String, ProgramType>,
    /// The slice iterators that are values of the library's `SliceIter`,
    /// with their element types.
    library_slice_iterators: BTreeMap<String, Type>,
    /// The `Option<&T>` locals library slice iterators' `next()` returns,
    /// with their element types.
    library_slice_options: BTreeMap<String, Type>,
    /// Each library slice iterator's `next()` result local.
    library_next_options: BTreeMap<String, String>,
    /// The library `chunks_exact` iterators built in place, whose
    /// `remainder(&it)` is read where they are built.
    library_chunk_built: BTreeSet<String>,
    /// The range locals, with their element type.
    ranges: BTreeMap<String, (Type, bool)>,
    /// The enumerated slice iterators and their `Option` locals.
    enumerated: BTreeSet<String>,
    shared_array_options: BTreeMap<String, ProgramType>,
    shared_scalar_slices: BTreeMap<String, (String, ProgramType)>,
    mir_chunk_iterators: BTreeSet<String>,
    chunk_options: BTreeSet<String>,
    local_arrays: BTreeSet<String>,
    owned_locals: BTreeSet<String>,
    /// Integer and `bool` locals, which a borrow takes the address of.
    addressable_locals: BTreeSet<String>,
    /// The enum and type-parameter locals the body borrows, with the C type
    /// of their value. Such a value otherwise lives in its local's binding;
    /// these live in their object's memory, so a write through the borrow
    /// is the value later reads see.
    memory_values: BTreeMap<String, ProgramType>,
    slices: BTreeMap<String, (String, bool)>,
    arrays: BTreeMap<String, (u64, ProgramType, bool)>,
    references: BTreeMap<String, bool>,
    source: &'a str,
    function: &'a str,
    fields: &'a BTreeMap<(&'a str, &'a str), (u32, ProgramType)>,
    next_load: u32,
    import_identity: Option<std::sync::Arc<str>>,
    mir_point: Option<super::borrow_frontiers::MirPoint>,
    mir_nodes: BTreeMap<usize, usize>,
    next_temporary: u32,
    /// The iterator each loop advances, by loop index in preorder.
    loop_iterators: Vec<Option<crate::languages::interface::RustLoopIterator>>,
    locals: BTreeSet<String>,
    return_type: InterfaceType,
    layouts: &'a BTreeMap<String, RecordLayout>,
    records: &'a BTreeMap<&'a str, &'a Record>,
    functions: &'a BTreeMap<&'a str, &'a Function>,
}
impl Context<'_> {
    fn reference_source(
        &self,
        expr: &E,
        kind: ReferenceAccessKind,
    ) -> Option<ReferenceAccessSourceId> {
        let point = self.mir_point?;
        let import_identity = self.import_identity.clone()?;
        let E::Deref { reference, .. } = expr else {
            return None;
        };
        let E::Local { name } = reference.as_ref() else {
            return None;
        };
        let node = *self.mir_nodes.get(&(expr as *const E as usize))?;
        Some(ReferenceAccessSourceId {
            import_identity,
            function: self.function.into(),
            block: point.block,
            statement: point.statement,
            node,
            reference_local: name.as_str().into(),
            kind,
        })
    }
    fn source_store(
        &self,
        target: &E,
        pointer: ProgramExpression,
        value: ProgramExpression,
        value_type: ProgramType,
    ) -> ProgramStatement {
        let mut statement = program_typed_store(pointer, value, value_type);
        if let ProgramStatement::TypedStore { source, .. } = &mut statement
            && let Some(id) = self.reference_source(target, ReferenceAccessKind::Write)
        {
            *source = StatementStoreSource::new(id);
        }
        statement
    }
    fn body(&mut self, body: &[S]) -> Result<ProgramStatement, String> {
        let mut result = program_skip();
        for s in body {
            result = program_seq(result, self.statement(s)?);
        }
        Ok(result)
    }
    fn statement(&mut self, s: &S) -> Result<ProgramStatement, String> {
        match s {
            S::SliceSplit {
                slice,
                midpoint,
                left,
                right,
            } => self.slice_split(slice, midpoint, left, right),
            S::SliceFor {
                iterator,
                slice,
                binding,
                by_reference,
                body,
            } => self.slice_for(iterator, slice, binding, *by_reference, body),
            S::Declare { place, initializer } => {
                if let Type::Reference { mutable, .. } = &place.value_type {
                    self.references.insert(place.name.clone(), !mutable);
                }
                if !self.locals.insert(place.name.clone()) {
                    return Err("duplicate Rust local identity".into());
                }
                if let Type::Array { element, length } = &place.value_type {
                    return self.declare_array(&place.name, element, *length, initializer);
                }
                if let Type::ByteSlice { mutable } = &place.value_type {
                    let (pointer, length_value) = self.slice_parts(initializer)?;
                    let length = format!("{}_len", place.name);
                    if !self.locals.insert(length.clone()) {
                        return Err("slice local length collision".into());
                    }
                    self.slices
                        .insert(place.name.clone(), (length.clone(), !mutable));
                    return Ok(program_seq(
                        program_declare_with_all_qualifiers(
                            &place.name,
                            ProgramType::UInt8Pointer,
                            false,
                            false,
                            false,
                            !mutable,
                        ),
                        program_seq(
                            program_declare(&length, ProgramType::UInt64),
                            program_seq(
                                program_assign(
                                    &place.name,
                                    reference_view(
                                        pointer,
                                        ProgramType::UInt8Pointer,
                                        false,
                                        !mutable,
                                    ),
                                ),
                                program_assign(length, length_value),
                            ),
                        ),
                    ));
                }
                if let Type::Reference { mutable, pointee } = &place.value_type
                    && let Type::Array { element, length } = pointee.as_ref()
                {
                    let (pointer, source_length, source_element) =
                        self.indexed_parts(initializer)?;
                    if source_length != crate::kernel::program_expression::uint64_literal(*length)
                        || source_element != scalar_type(element)?.to_kernel_type()
                    {
                        return Err("fixed array local disagrees with initializer".into());
                    }
                    let t = scalar_type(&place.value_type)?.to_kernel_type();
                    self.arrays
                        .insert(place.name.clone(), (*length, source_element, !mutable));
                    return Ok(program_seq(
                        program_declare_with_all_qualifiers(
                            &place.name,
                            t,
                            false,
                            false,
                            false,
                            !mutable,
                        ),
                        program_assign(&place.name, reference_view(pointer, t, false, !mutable)),
                    ));
                }
                let t = scalar_type(&place.value_type)?;
                if t == InterfaceType::Void {
                    return Err("unit locals outside Rust slice".into());
                }
                let constant = matches!(place.value_type, Type::Reference { mutable: false, .. });
                let declaration = program_declare_with_all_qualifiers(
                    &place.name,
                    t.to_kernel_type(),
                    false,
                    false,
                    false,
                    constant,
                );
                let assign = self.assign(&place.name, initializer)?;
                Ok(program_seq(declaration, assign))
            }
            S::Assign {
                target: E::Local { name },
                value,
            } => self.assign(name, value),
            S::Assign { target, value } => {
                if let E::Deref {
                    value_type: Type::Array { element, length },
                    ..
                } = target
                {
                    let (checks, pointer) = self.prepared_address(target)?;
                    return Ok(program_seq(
                        checks,
                        self.assign_array(
                            pointer,
                            scalar_type(element)?.to_kernel_type(),
                            *length,
                            value,
                        )?,
                    ));
                }
                let (mut checks, mut value) = self.prepared_expr(value)?;
                if matches!(target, E::Index { .. }) {
                    // Rust evaluates the RHS before the destination index,
                    // which may call a function that changes the RHS storage.
                    let value_type = indexed_element_type(self.place_type(target)?)
                        .ok_or("unsupported Rust indexed assignment type")?;
                    let (capture, name) = self.capture_operand(value, &value_type)?;
                    checks = program_seq(checks, capture);
                    value = crate::kernel::program_expression::variable(name);
                }
                let (target_checks, address) = self.prepared_address(target)?;
                Ok(program_seq(
                    program_seq(checks, target_checks),
                    program_typed_store(address, value, self.place_type(target)?),
                ))
            }
            S::While { condition, body } => {
                fn simple_guard(expression: &E) -> bool {
                    match expression {
                        E::Integer { .. }
                        | E::UnsignedInteger { .. }
                        | E::SignedInteger { .. }
                        | E::UsizeInteger { .. }
                        | E::Boolean { .. }
                        | E::Local { .. }
                        | E::SliceLength { .. } => true,
                        E::Not { value } | E::Cast { value, .. } | E::IntegerFrom { value, .. } => {
                            simple_guard(value)
                        }
                        E::Binary {
                            operator,
                            left,
                            right,
                            ..
                        } => {
                            matches!(
                                operator.as_str(),
                                "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
                            ) && simple_guard(left)
                                && simple_guard(right)
                        }
                        _ => false,
                    }
                }
                if !simple_guard(condition) {
                    return Err("Rust while conditions currently require scalar comparisons without calls, indexing or arithmetic".into());
                }
                Ok(program_while(
                    branch_condition(self.expr(condition)?),
                    Vec::new(),
                    self.body(body)?,
                ))
            }
            S::If {
                condition,
                then_body,
                else_body,
            } => {
                let (checks, condition) = self.prepared_expr(condition)?;
                Ok(program_seq(
                    checks,
                    program_if(
                        branch_condition(condition),
                        self.body(then_body)?,
                        self.body(else_body)?,
                    ),
                ))
            }
            S::Return {
                value:
                    Some(E::Call {
                        function,
                        arguments,
                    }),
            } => {
                let mut name = "__rust_return_value".to_string();
                while self.locals.contains(&name) {
                    name.push('_');
                }
                self.locals.insert(name.clone());
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(program_seq(
                    checks,
                    program_seq(
                        program_declare(&name, self.return_type.to_kernel_type()),
                        program_seq(
                            program_call_assign(&name, function, arguments),
                            program_return(crate::kernel::program_expression::variable(name)),
                        ),
                    ),
                ))
            }
            S::Return { value: Some(value) } => {
                let (checks, value) = self.prepared_expr(value)?;
                Ok(program_seq(checks, program_return(value)))
            }
            S::Return { value: None } if self.return_type == InterfaceType::Void => {
                Ok(program_return(program_void_value()))
            }
            S::Return { value: None } => Err("missing Rust return value".into()),
            S::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(program_seq(checks, program_call(function, arguments)))
            }
        }
    }
    fn slice_split(
        &mut self,
        slice: &E,
        midpoint: &E,
        left: &super::schema::Place,
        right: &super::schema::Place,
    ) -> Result<ProgramStatement, String> {
        self.slice_split_slots(slice, midpoint, left, right, true)
    }
    fn slice_split_slots(
        &mut self,
        slice: &E,
        midpoint: &E,
        left: &super::schema::Place,
        right: &super::schema::Place,
        declare: bool,
    ) -> Result<ProgramStatement, String> {
        if left.name == right.name {
            return Err("split_at results require distinct slice slots".into());
        }
        let E::Local { name } = slice else {
            return Err("split_at requires a shared byte-slice local".into());
        };
        if !self.slices.get(name).is_some_and(|(_, constant)| *constant) {
            return Err("split_at requires a shared byte-slice local".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        // Evaluate the receiver before the argument and capture both metadata
        // components. The midpoint may call code; it is evaluated only once.
        let (pointer_capture, pointer_name) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (length_capture, length_name) = self.capture_operand(length, &Type::Usize)?;
        let (midpoint_prefix, midpoint_value) = self.prepared_expr(midpoint)?;
        let (midpoint_capture, midpoint_name) =
            self.capture_operand(midpoint_value, &Type::Usize)?;
        let mut result = program_seq(
            pointer_capture,
            program_seq(
                length_capture,
                program_seq(midpoint_prefix, midpoint_capture),
            ),
        );
        result = program_seq(
            result,
            program_labeled_assert(
                crate::kernel::program_expression::less_equal(
                    crate::kernel::program_expression::variable(&midpoint_name),
                    crate::kernel::program_expression::variable(&length_name),
                ),
                "Rust split_at panic check",
            ),
        );
        for (place, pointer, length) in [
            (
                left,
                crate::kernel::program_expression::variable(&pointer_name),
                crate::kernel::program_expression::variable(&midpoint_name),
            ),
            (
                right,
                // The right half starts at the midpoint in its own type, as
                // the contract's `bytes[mid]` does.
                crate::kernel::program_expression::add(
                    crate::kernel::program_expression::variable(&pointer_name),
                    crate::kernel::program_expression::variable(&midpoint_name),
                ),
                crate::kernel::program_expression::subtract(
                    crate::kernel::program_expression::variable(&length_name),
                    crate::kernel::program_expression::variable(&midpoint_name),
                ),
            ),
        ] {
            if place.value_type != (Type::ByteSlice { mutable: false }) {
                return Err("split_at results must be shared byte slices".into());
            }
            let length_name = if declare {
                let length_name = format!("{}_len", place.name);
                if !self.locals.insert(place.name.clone())
                    || !self.locals.insert(length_name.clone())
                {
                    return Err("duplicate split_at local identity".into());
                }
                self.slices
                    .insert(place.name.clone(), (length_name.clone(), true));
                result = program_seq(
                    result,
                    program_seq(
                        program_declare_with_all_qualifiers(
                            &place.name,
                            ProgramType::UInt8Pointer,
                            false,
                            false,
                            false,
                            true,
                        ),
                        program_declare(&length_name, ProgramType::UInt64),
                    ),
                );
                length_name
            } else {
                self.slices
                    .get(&place.name)
                    .filter(|(_, constant)| *constant)
                    .map(|(length, _)| length.clone())
                    .ok_or("split_at requires declared shared slice results")?
            };
            result = program_seq(
                result,
                program_seq(
                    program_assign(
                        &place.name,
                        reference_view(pointer, ProgramType::UInt8Pointer, false, true),
                    ),
                    program_assign(length_name, length),
                ),
            );
        }
        Ok(result)
    }
    // Semantic slice-iterator state: cursor plus remaining slice length.
    // The signed length is the shared memory model's checked representation,
    // not a generated count of processed elements.
    fn slice_for(
        &mut self,
        iterator: &str,
        slice: &E,
        binding: &super::schema::Place,
        by_reference: bool,
        body: &[S],
    ) -> Result<ProgramStatement, String> {
        let (pointer, length) = self.slice_parts(slice)?;
        let cursor = format!("{iterator}_cursor");
        let remaining = format!("{iterator}_remaining");
        let item = format!("{iterator}_item");
        for name in [&cursor, &remaining, &item, &binding.name] {
            if !self.locals.insert(name.clone()) {
                return Err("Rust iterator state identity collision".into());
            }
        }
        let expected = if by_reference {
            Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            }
        } else {
            Type::U8
        };
        if binding.value_type != expected {
            return Err("Rust iterator yielded binding type mismatch".into());
        }
        let declaration = program_declare_with_all_qualifiers(
            &binding.name,
            scalar_type(&binding.value_type)?.to_kernel_type(),
            false,
            false,
            false,
            by_reference,
        );
        // Save Some's shared address before advancing. Copy patterns likewise
        // read that address before the source body; None does neither operation.
        let yielded = if by_reference {
            crate::kernel::program_expression::variable(&item)
        } else {
            let occurrence = self.next_load;
            self.next_load = self
                .next_load
                .checked_add(1)
                .ok_or("Rust load identity exhausted")?;
            crate::kernel::program_expression::typed_load_with_source(
                crate::kernel::program_expression::variable(&item),
                ProgramType::UInt8,
                Some(LoadSourceId {
                    owner: LoadSourceOwnerId {
                        source_unit: self.source.into(),
                        function: self.function.into(),
                    },
                    occurrence,
                    reference_access: None,
                }),
            )
        };
        // The remaining count is the slice's length, a `usize`.
        let next = program_seq(
            program_declare_with_all_qualifiers(
                &item,
                ProgramType::UInt8Pointer,
                false,
                false,
                false,
                true,
            ),
            program_seq(
                program_assign(&item, crate::kernel::program_expression::variable(&cursor)),
                program_seq(
                    program_assign(
                        &cursor,
                        crate::kernel::program_expression::add(
                            crate::kernel::program_expression::variable(&cursor),
                            crate::kernel::program_expression::int32_literal(1),
                        ),
                    ),
                    program_seq(
                        program_assign(
                            &remaining,
                            crate::kernel::program_expression::subtract(
                                crate::kernel::program_expression::variable(&remaining),
                                crate::kernel::program_expression::uint64_literal(1),
                            ),
                        ),
                        program_seq(declaration, program_assign(&binding.name, yielded)),
                    ),
                ),
            ),
        );
        let source_body = self.body(body)?;
        Ok(program_seq(
            program_declare_with_all_qualifiers(
                &cursor,
                ProgramType::UInt8Pointer,
                false,
                false,
                false,
                true,
            ),
            program_seq(
                program_assign(&cursor, pointer),
                program_seq(
                    program_declare(&remaining, ProgramType::UInt64),
                    program_seq(
                        program_assign(&remaining, length),
                        program_while(
                            crate::kernel::program_expression::not(
                                crate::kernel::program_expression::equal(
                                    crate::kernel::program_expression::variable(&remaining),
                                    crate::kernel::program_expression::uint64_literal(0),
                                ),
                            ),
                            Vec::new(),
                            program_seq(next, source_body),
                        ),
                    ),
                ),
            ),
        ))
    }
    fn assign(&mut self, name: &str, e: &E) -> Result<ProgramStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        // A memory-backed local's value is computed into a temporary and
        // stored to its object.
        if let Some(&value_type) = self.memory_values.get(name) {
            let temporary = self.fresh_temporary()?;
            let assign = self.assign(&temporary, e)?;
            let address = self.address(&E::Local { name: name.into() })?;
            return Ok(program_seq(
                program_seq(program_declare(&temporary, value_type), assign),
                program_typed_store(
                    address,
                    crate::kernel::program_expression::variable(&temporary),
                    value_type,
                ),
            ));
        }
        if let Some((length, expected)) = self.shared_scalar_slices.get(name).cloned() {
            let (pointer, source_length, element) = self.indexed_parts(e)?;
            if element != expected {
                return Err("shared scalar slice assignment element mismatch".into());
            }
            return Ok(program_seq(
                program_assign(name, pointer),
                program_assign(length, source_length),
            ));
        }
        if self.local_arrays.contains(name) {
            let (length, element, _) = self.arrays[name];
            return self.assign_array(self.array_pointer(name)?, element, length, e);
        }
        if let Some((length, constant)) = self.slices.get(name).cloned() {
            let checks = self.chunk_slice_checks(e)?;
            let (pointer, length_value) = self.slice_parts(e)?;
            return Ok(program_seq(
                checks,
                program_seq(
                    program_assign(
                        name,
                        reference_view(pointer, ProgramType::UInt8Pointer, false, constant),
                    ),
                    program_assign(length, length_value),
                ),
            ));
        }
        if let Some((length, element, constant)) = self.arrays.get(name).copied() {
            let (pointer, source_length, source_element) = self.indexed_parts(e)?;
            if source_length != crate::kernel::program_expression::uint64_literal(length)
                || source_element != element
            {
                return Err("fixed array assignment disagrees with destination".into());
            }
            let pointer_type = match element {
                ProgramType::Int32 => ProgramType::Int32Pointer,
                ProgramType::UInt8 => ProgramType::UInt8Pointer,
                ProgramType::UInt32 => ProgramType::UInt32Pointer,
                _ => return Err("unsupported fixed array element".into()),
            };
            return Ok(program_assign(
                name,
                reference_view(pointer, pointer_type, false, constant),
            ));
        }
        match e {
            E::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(program_seq(
                    checks,
                    program_call_assign(name, function, arguments),
                ))
            }
            _ => {
                let (checks, value) = self.prepared_expr(e)?;
                let mut assignment = program_assign(name, value);
                if let (
                    Some(import_identity),
                    Some(point),
                    E::Borrow {
                        place,
                        value_type:
                            Type::Reference {
                                mutable: true,
                                pointee,
                            },
                    },
                ) = (&self.import_identity, self.mir_point, e)
                    && matches!(
                        pointee.as_ref(),
                        Type::I32 | Type::U8 | Type::U16 | Type::U32
                    )
                    && let E::Deref { reference, .. } = place.as_ref()
                    && let E::Local { name: parent } = reference.as_ref()
                    && let ProgramStatement::Assign { source, .. } = &mut assignment
                {
                    *source = StatementAssignSource::new(ReferenceBorrowSourceId {
                        import_identity: import_identity.clone(),
                        function: self.function.into(),
                        block: point.block,
                        statement: point.statement,
                        parent: parent.as_str().into(),
                        child: name.into(),
                    });
                }
                Ok(program_seq(checks, assignment))
            }
        }
    }
    fn prepared_arguments(
        &mut self,
        function: &str,
        args: &[E],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>), String> {
        let types = self
            .functions
            .get(function)
            .ok_or("missing Rust call definition")?
            .parameters
            .iter()
            .map(|p| p.value_type.clone())
            .collect::<Vec<_>>();
        self.typed_arguments(types, args)
    }

    /// Arguments checked against the parameter types they are passed for.
    fn typed_arguments(
        &mut self,
        types: Vec<Type>,
        args: &[E],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>), String> {
        if types.len() != args.len() {
            return Err("Rust call argument count disagrees with callee".into());
        }
        let mut checks = program_skip();
        let mut values = Vec::new();
        for (argument, value_type) in args.iter().zip(types) {
            if matches!(value_type, Type::Record { .. }) {
                let E::Local { name } = argument else {
                    return Err("owned call operand must be a MIR local".into());
                };
                if !self.owned_locals.contains(name) {
                    return Err("owned call operand has no local storage".into());
                }
                values.push(crate::kernel::program_expression::variable(name));
                continue;
            }
            if let Type::ByteSlice { mutable } = value_type {
                let (pointer, length) = self.slice_parts(argument)?;
                let (capture_pointer, pointer_name) = self.capture_operand(
                    pointer,
                    &Type::Reference {
                        mutable,
                        pointee: Box::new(Type::U8),
                    },
                )?;
                let (capture_length, length_name) = self.capture_operand(length, &Type::Usize)?;
                checks = program_seq(checks, program_seq(capture_pointer, capture_length));
                values.extend([
                    crate::kernel::program_expression::variable(pointer_name),
                    crate::kernel::program_expression::variable(length_name),
                ]);
                continue;
            }
            if let Type::ScalarSlice { element, mutable } = &value_type {
                let (pointer, length, actual) = self.indexed_parts(argument)?;
                if actual != scalar_type(element)?.to_kernel_type() {
                    return Err("Rust scalar slice call element mismatch".into());
                }
                let (capture_pointer, pointer_name) = self.capture_operand(
                    pointer,
                    &Type::Reference {
                        mutable: *mutable,
                        pointee: element.clone(),
                    },
                )?;
                let (capture_length, length_name) = self.capture_operand(length, &Type::Usize)?;
                checks = program_seq(checks, program_seq(capture_pointer, capture_length));
                values.extend([
                    crate::kernel::program_expression::variable(pointer_name),
                    crate::kernel::program_expression::variable(length_name),
                ]);
                continue;
            }
            let (prefix, value) = self.prepared_expr(argument)?;
            let (capture, name) = self.capture_operand(value, &value_type)?;
            checks = program_seq(checks, program_seq(prefix, capture));
            values.push(crate::kernel::program_expression::variable(name));
        }
        Ok((checks, values))
    }

    /// A fresh local name for a value the lowering introduces.
    fn fresh_temporary(&mut self) -> Result<String, String> {
        loop {
            let name = format!("__rust_checked_{}", self.next_temporary);
            self.next_temporary = self
                .next_temporary
                .checked_add(1)
                .ok_or("Rust temporary identity exhausted")?;
            if self.locals.insert(name.clone()) {
                return Ok(name);
            }
        }
    }
    fn capture_operand(
        &mut self,
        value: ProgramExpression,
        value_type: &Type,
    ) -> Result<(ProgramStatement, String), String> {
        let name = self.fresh_temporary()?;
        let interface_type = scalar_type(value_type)?.to_kernel_type();
        let constant = matches!(value_type, Type::Reference { mutable: false, .. });
        let value = if matches!(value_type, Type::Reference { .. }) {
            reference_view(value, interface_type, false, constant)
        } else {
            crate::kernel::program_expression::cast(value, interface_type)
        };
        Ok((
            program_seq(
                program_declare_with_all_qualifiers(
                    &name,
                    interface_type,
                    false,
                    false,
                    false,
                    constant,
                ),
                program_assign(&name, value),
            ),
            name,
        ))
    }

    // Capture each operand once, in source order. Guards reference those
    // small names rather than duplicating arbitrarily large expression trees.
    // The generated asserts are checked execution obligations, not assumptions.
    fn prepared_expr(&mut self, e: &E) -> Result<(ProgramStatement, ProgramExpression), String> {
        match e {
            E::EnumerateOptionIndex { option } => self.enumerate_option_index(option),
            // The `Some` payload of a library iterator's `Option<&T>`: the
            // test that led here established the variant.
            E::SharedArrayOptionElement { option }
                if self.library_slice_options.contains_key(option) =>
            {
                Ok((
                    program_skip(),
                    ProgramExpression::EnumField {
                        value: Box::new(crate::kernel::program_expression::variable(option)),
                        variant: "Some".into(),
                        index: 0,
                    },
                ))
            }
            E::SharedArrayOptionElement { option } => {
                if !self.shared_array_options.contains_key(option) {
                    return Err("unknown shared iterator Option".into());
                }
                Ok((
                    program_assert(crate::kernel::program_expression::equal(
                        crate::kernel::program_expression::variable(format!("{option}_some")),
                        crate::kernel::program_expression::int32_literal(1),
                    )),
                    crate::kernel::program_expression::variable(format!("{option}_pointer")),
                ))
            }
            E::Call {
                function,
                arguments,
            } => {
                let return_type = self
                    .functions
                    .get(function.as_str())
                    .ok_or("missing Rust call definition")?
                    .return_type
                    .clone();
                let (prefix, arguments) = self.prepared_arguments(function, arguments)?;
                let (declare, name) = self.capture_operand(
                    crate::kernel::program_expression::int32_literal(0),
                    &return_type,
                )?;
                Ok((
                    program_seq(
                        prefix,
                        program_seq(declare, program_call_assign(&name, function, arguments)),
                    ),
                    crate::kernel::program_expression::variable(name),
                ))
            }
            E::Index { .. } => {
                let (checks, pointer) = self.prepared_address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok((
                    checks,
                    crate::kernel::program_expression::typed_load_with_source(
                        pointer,
                        self.place_type(e)?,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source.into(),
                                function: self.function.into(),
                            },
                            occurrence,
                            reference_access: None,
                        }),
                    ),
                ))
            }
            E::Borrow { place, value_type } if matches!(place.as_ref(), E::Index { .. }) => {
                let (checks, pointer) = self.prepared_address(place)?;
                Ok((
                    checks,
                    reference_view(
                        pointer,
                        scalar_type(value_type)?.to_kernel_type(),
                        false,
                        false,
                    ),
                ))
            }
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } => {
                let (left_prefix, left_value) = self.prepared_expr(left)?;
                let (left_capture, left_name) = self.capture_operand(left_value, left_type)?;
                let prefix = program_seq(left_prefix, left_capture);
                if operator == "and" || operator == "or" {
                    if *left_type != Type::Bool || *right_type != Type::Bool {
                        return Err("Rust logical operators require bool operands".into());
                    }
                    let (right_prefix, right_value) = self.prepared_expr(right)?;
                    let condition = if operator == "and" {
                        crate::kernel::program_expression::variable(&left_name)
                    } else {
                        crate::kernel::program_expression::not(
                            crate::kernel::program_expression::variable(&left_name),
                        )
                    };
                    let update = program_seq(
                        right_prefix,
                        program_assign(
                            &left_name,
                            crate::kernel::program_expression::cast(right_value, ProgramType::Bool),
                        ),
                    );
                    return Ok((
                        program_seq(prefix, program_if(condition, update, program_skip())),
                        crate::kernel::program_expression::variable(left_name),
                    ));
                }
                let (right_prefix, right_value) = self.prepared_expr(right)?;
                let (right_capture, right_name) = self.capture_operand(right_value, right_type)?;
                let mut prefix = program_seq(prefix, program_seq(right_prefix, right_capture));
                if matches!(left_type, Type::Usize | Type::U64) {
                    let l = crate::kernel::program_expression::variable(&left_name);
                    let r = crate::kernel::program_expression::variable(&right_name);
                    let max = crate::kernel::program_expression::uint64_literal(u64::MAX);
                    // Stay unsigned at the full target width. Widening to
                    // signed i64 would lose half of the usize value range.
                    let obligation = match operator.as_str() {
                        "add" => Some(crate::kernel::program_expression::less_equal(
                            l,
                            crate::kernel::program_expression::subtract(max, r),
                        )),
                        "sub" => Some(crate::kernel::program_expression::greater_equal(l, r)),
                        "mul" => Some(crate::kernel::program_expression::or(
                            crate::kernel::program_expression::equal(
                                r.clone(),
                                crate::kernel::program_expression::uint64_literal(0),
                            ),
                            crate::kernel::program_expression::less_equal(
                                l,
                                crate::kernel::program_expression::divide(max, r),
                            ),
                        )),
                        "shl" | "shr" => Some(crate::kernel::program_expression::less_than(
                            crate::kernel::program_expression::cast(r, ProgramType::UInt64),
                            crate::kernel::program_expression::uint64_literal(64),
                        )),
                        _ => None,
                    };
                    if let Some(obligation) = obligation {
                        prefix = program_seq(
                            prefix,
                            program_labeled_assert(
                                obligation,
                                format!("Rust {operator} panic check"),
                            ),
                        );
                    }
                }
                // A signed shift panics in Rust unless its count is below
                // the operand's width. C checks only the promoted word's
                // width, which for `i8` and `i16` is 32, so the check is
                // explicit; a negative count is a large unsigned one.
                if left_type.is_signed_integer() && matches!(operator.as_str(), "shl" | "shr") {
                    let width = left_type
                        .integer_bits()
                        .ok_or("Rust signed shift operand has no width")?;
                    let count = crate::kernel::program_expression::variable(&right_name);
                    let obligation = if right_type.integer_bits() == Some(64) {
                        crate::kernel::program_expression::less_than(
                            crate::kernel::program_expression::cast(count, ProgramType::UInt64),
                            crate::kernel::program_expression::uint64_literal(width.into()),
                        )
                    } else {
                        crate::kernel::program_expression::less_than(
                            crate::kernel::program_expression::cast(count, ProgramType::UInt32),
                            crate::kernel::program_expression::uint32_literal(width),
                        )
                    };
                    prefix = program_seq(
                        prefix,
                        program_labeled_assert(obligation, format!("Rust {operator} panic check")),
                    );
                }
                // Narrow signed arithmetic is computed in `int`, where it
                // cannot overflow; Rust panics unless the result fits.
                if matches!(left_type, Type::I8 | Type::I16)
                    && matches!(operator.as_str(), "add" | "sub" | "mul")
                {
                    let l = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&left_name),
                        ProgramType::Int32,
                    );
                    let r = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&right_name),
                        ProgramType::Int32,
                    );
                    let (minimum, maximum) = match left_type {
                        Type::I8 => (i8::MIN as i64, i8::MAX as i64),
                        _ => (i16::MIN as i64, i16::MAX as i64),
                    };
                    let wide = |value: ProgramExpression| {
                        crate::kernel::program_expression::cast(value, ProgramType::Int64)
                    };
                    let value = match operator.as_str() {
                        "add" => crate::kernel::program_expression::add(wide(l), wide(r)),
                        "sub" => crate::kernel::program_expression::subtract(wide(l), wide(r)),
                        _ => crate::kernel::program_expression::multiply(wide(l), wide(r)),
                    };
                    prefix = program_seq(
                        prefix,
                        program_labeled_assert(
                            crate::kernel::program_expression::and(
                                crate::kernel::program_expression::greater_equal(
                                    value.clone(),
                                    crate::kernel::program_expression::int64_literal(minimum),
                                ),
                                crate::kernel::program_expression::less_equal(
                                    value,
                                    crate::kernel::program_expression::int64_literal(maximum),
                                ),
                            ),
                            format!("Rust {operator} panic check"),
                        ),
                    );
                }
                // So is narrow signed division: `MIN / -1` fits `int`, but
                // Rust panics on it, and on its remainder.
                if matches!(left_type, Type::I8 | Type::I16)
                    && matches!(operator.as_str(), "div" | "rem")
                {
                    let minimum = match left_type {
                        Type::I8 => i8::MIN as i32,
                        _ => i16::MIN as i32,
                    };
                    let l = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&left_name),
                        ProgramType::Int32,
                    );
                    let r = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&right_name),
                        ProgramType::Int32,
                    );
                    prefix = program_seq(
                        prefix,
                        program_labeled_assert(
                            crate::kernel::program_expression::not(
                                crate::kernel::program_expression::and(
                                    crate::kernel::program_expression::equal(
                                        l,
                                        crate::kernel::program_expression::int32_literal(
                                            minimum as u32,
                                        ),
                                    ),
                                    crate::kernel::program_expression::equal(
                                        r,
                                        crate::kernel::program_expression::int32_literal(
                                            -1i32 as u32,
                                        ),
                                    ),
                                ),
                            ),
                            format!("Rust {operator} panic check"),
                        ),
                    );
                }
                if matches!(left_type, Type::U8 | Type::U16 | Type::U32) {
                    let l = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&left_name),
                        ProgramType::UInt32,
                    );
                    let r = crate::kernel::program_expression::cast(
                        crate::kernel::program_expression::variable(&right_name),
                        ProgramType::UInt32,
                    );
                    let width = match left_type {
                        Type::U8 => 8,
                        Type::U16 => 16,
                        _ => 32,
                    };
                    let maximum = match left_type {
                        Type::U8 => 255,
                        Type::U16 => 65535,
                        _ => u32::MAX,
                    };
                    let max = crate::kernel::program_expression::uint32_literal(maximum);
                    // Stay unsigned, as `usize` does: `max - r` cannot wrap,
                    // and a guard such as `l < n` then bounds `l` directly.
                    let obligation = match operator.as_str() {
                        "add" => Some(crate::kernel::program_expression::less_equal(
                            l,
                            crate::kernel::program_expression::subtract(max.clone(), r),
                        )),
                        "sub" => Some(crate::kernel::program_expression::greater_equal(l, r)),
                        "mul" => Some(crate::kernel::program_expression::or(
                            crate::kernel::program_expression::equal(
                                r.clone(),
                                crate::kernel::program_expression::uint32_literal(0),
                            ),
                            crate::kernel::program_expression::less_equal(
                                l,
                                crate::kernel::program_expression::divide(max, r),
                            ),
                        )),
                        "shl" | "shr" => Some(if right_type.integer_bits() == Some(64) {
                            crate::kernel::program_expression::less_than(
                                crate::kernel::program_expression::cast(
                                    crate::kernel::program_expression::variable(&right_name),
                                    ProgramType::UInt64,
                                ),
                                crate::kernel::program_expression::uint64_literal(width),
                            )
                        } else {
                            crate::kernel::program_expression::less_than(
                                r,
                                crate::kernel::program_expression::uint32_literal(width as u32),
                            )
                        }),
                        _ => None,
                    };
                    if let Some(obligation) = obligation {
                        prefix = program_seq(
                            prefix,
                            program_labeled_assert(
                                obligation,
                                format!("Rust {operator} panic check"),
                            ),
                        );
                    }
                }
                let expression = E::Binary {
                    operator: operator.clone(),
                    left_type: left_type.clone(),
                    right_type: right_type.clone(),
                    left: Box::new(E::Local { name: left_name }),
                    right: Box::new(E::Local { name: right_name }),
                };
                Ok((prefix, self.expr(&expression)?))
            }
            E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::IntegerFrom { value, .. } => {
                let (prefix, value) = self.prepared_expr(value)?;
                let value = match e {
                    E::Not { .. } => crate::kernel::program_expression::bool_value(
                        crate::kernel::program_expression::not(value),
                    ),
                    E::BitwiseNot { value_type, .. } => {
                        rust_bitwise_not(value, scalar_type(value_type)?.to_kernel_type())
                    }
                    E::Cast { value_type, .. } => {
                        rust_scalar_cast(value, scalar_type(value_type)?.to_kernel_type())
                    }
                    E::IntegerFrom {
                        source_type,
                        value_type,
                        ..
                    } => integer_from(value, source_type, value_type)?,
                    _ => unreachable!(),
                };
                Ok((prefix, value))
            }
            _ => Ok((program_skip(), self.expr(e)?)),
        }
    }
    fn slice_parts(&mut self, e: &E) -> Result<(ProgramExpression, ProgramExpression), String> {
        if let E::ChunkOptionSlice { option } = e {
            if !self.chunk_options.contains(option) {
                return Err("unknown chunk Option".into());
            }
            return Ok((
                crate::kernel::program_expression::variable(format!("{option}_pointer")),
                crate::kernel::program_expression::variable(format!("{option}_len")),
            ));
        }
        if let E::Borrow {
            place,
            value_type: Type::ByteSlice { mutable },
        } = e
        {
            let E::Local { name } = place.as_ref() else {
                return Err("slice reborrow requires a slice local".into());
            };
            if *mutable && self.slices.get(name).is_none_or(|(_, constant)| *constant) {
                return Err("mutable slice reborrow requires a mutable source".into());
            }
            return self.slice_parts(place);
        }
        if let E::ChunkRemainder { iterator } = e {
            if !self.mir_chunk_iterators.contains(iterator) {
                return Err("unknown Rust chunk iterator".into());
            }
            return Ok((
                crate::kernel::program_expression::variable(format!("{iterator}_tail")),
                crate::kernel::program_expression::variable(format!("{iterator}_tail_len")),
            ));
        }
        if let E::ArrayToSlice { array, mutable } = e {
            let (pointer, length, element) = self.indexed_parts(array)?;
            if element != ProgramType::UInt8 {
                return Err("array coercion requires u8 elements".into());
            }
            let constant = self.array_source_is_constant(array)?;
            if *mutable && constant {
                return Err("mutable array coercion requires a mutable source".into());
            }
            return Ok((pointer, length));
        }
        let E::Local { name } = e else {
            return Err("slice values must be local slice references".into());
        };
        let (length, _) = self
            .slices
            .get(name)
            .ok_or("unknown Rust slice reference")?;
        Ok((
            crate::kernel::program_expression::variable(name),
            crate::kernel::program_expression::variable(length),
        ))
    }
    fn array_source_is_constant(&self, e: &E) -> Result<bool, String> {
        match e {
            E::Local { name } => self
                .arrays
                .get(name)
                .map(|a| a.2)
                .ok_or("unknown array source".into()),
            E::Deref { reference, .. } => self.array_source_is_constant(reference),
            E::Field { base, .. } => match base.as_ref() {
                E::Local { name } if self.owned_locals.contains(name) => Ok(false),
                E::Deref { reference, .. } => match reference.as_ref() {
                    E::Local { name } => self
                        .references
                        .get(name)
                        .copied()
                        .ok_or("unknown record reference".into()),
                    _ => Err("array field requires a record reference local".into()),
                },
                _ => Err("array field requires a borrowed record".into()),
            },
            E::Borrow {
                value_type: Type::Reference { mutable, .. },
                ..
            } => Ok(!mutable),
            _ => Err("array coercion requires a fixed array place".into()),
        }
    }
    fn indexed_parts(
        &mut self,
        e: &E,
    ) -> Result<(ProgramExpression, ProgramExpression, ProgramType), String> {
        match e {
            E::Borrow { place, value_type } => {
                if matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                self.indexed_parts(place)
            }
            E::Deref { reference, .. } => self.indexed_parts(reference),
            E::Local { name } if self.shared_scalar_slices.contains_key(name) => {
                let (length, element) = self.shared_scalar_slices[name].clone();
                Ok((
                    crate::kernel::program_expression::variable(name),
                    crate::kernel::program_expression::variable(length),
                    element,
                ))
            }
            E::ArrayToSlice {
                array,
                mutable: false,
            } => self.indexed_parts(array),
            E::Local { name } if self.arrays.contains_key(name) => {
                let (length, element, _) = self.arrays[name];
                Ok((
                    self.array_pointer(name)?,
                    crate::kernel::program_expression::uint64_literal(length),
                    element,
                ))
            }
            E::Field { record, field, .. } => {
                let (_, ty) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust array field")?;
                let (element, length) =
                    array_field_parts(ty).ok_or("indexed Rust field is not a scalar array")?;
                let constant = self.array_source_is_constant(e)?;
                let pointer_type = match element {
                    ProgramType::Int32 => ProgramType::Int32Pointer,
                    ProgramType::UInt8 => ProgramType::UInt8Pointer,
                    ProgramType::UInt32 => ProgramType::UInt32Pointer,
                    _ => unreachable!(),
                };
                let pointer = self.address(e)?;
                Ok((
                    reference_view(pointer, pointer_type, false, constant),
                    crate::kernel::program_expression::uint64_literal(u64::from(length)),
                    element,
                ))
            }
            _ => {
                let (pointer, length) = self.slice_parts(e)?;
                Ok((pointer, length, ProgramType::UInt8))
            }
        }
    }
    fn array_pointer(&self, name: &str) -> Result<ProgramExpression, String> {
        let (_, element, constant) = self.arrays.get(name).ok_or("unknown fixed array")?;
        let pointer_type = match element {
            ProgramType::UInt8 => ProgramType::UInt8Pointer,
            ProgramType::UInt32 => ProgramType::UInt32Pointer,
            ProgramType::Int32 => ProgramType::Int32Pointer,
            _ => return Err("unsupported fixed array element".into()),
        };
        Ok(reference_view(
            crate::kernel::program_expression::variable(name),
            pointer_type,
            false,
            *constant,
        ))
    }
    fn prepared_address(&mut self, e: &E) -> Result<(ProgramStatement, ProgramExpression), String> {
        if let E::Index { slice, index } = e {
            let (pointer, length, _) = self.indexed_parts(slice)?;
            let (checks, value) = self.prepared_expr(index)?;
            let (capture, name) = self.capture_operand(value, &Type::Usize)?;
            let index = crate::kernel::program_expression::variable(name);
            // The index keeps its own type, as the contract's place does.
            let offset = index.clone();
            return Ok((
                program_seq(
                    checks,
                    program_seq(
                        capture,
                        program_labeled_assert(
                            crate::kernel::program_expression::less_than(index.clone(), length),
                            if matches!(slice.as_ref(), E::Local { name }
                                if self.slices.contains_key(name)
                                    || self.shared_scalar_slices.contains_key(name))
                            {
                                "Rust slice index panic check"
                            } else {
                                "Rust array index panic check"
                            },
                        ),
                    ),
                ),
                crate::kernel::program_expression::add(pointer, offset),
            ));
        }
        Ok((program_skip(), self.address(e)?))
    }
    fn address(&mut self, e: &E) -> Result<ProgramExpression, String> {
        match e {
            E::Local { name } if self.local_arrays.contains(name) => self.array_pointer(name),
            E::Deref { reference, .. } => self.expr(reference),
            E::Field {
                base,
                record,
                field,
            } => {
                let (offset, _) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust field")?;
                // Field bases are either record references or local stack objects.
                let pointer = match base.as_ref() {
                    E::Deref { reference, .. } => self.expr(reference)?,
                    _ => self.expr(base)?,
                };
                Ok(crate::kernel::program_expression::pointer_offset_bytes(
                    pointer, offset,
                ))
            }
            E::Local { name } if self.owned_locals.contains(name) => {
                Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(name),
                    ProgramType::Int32Pointer,
                ))
            }
            E::Local { name } if self.addressable_locals.contains(name) => {
                Ok(ProgramExpression::AddressOf(Box::new(
                    crate::kernel::program_expression::variable(name),
                )))
            }
            E::Local { name } if self.memory_values.contains_key(name) => {
                let ProgramType::Parameter(value_type) = self.memory_values[name] else {
                    return Err(
                        "a memory-backed Rust local holds an enum or type-parameter value".into(),
                    );
                };
                Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(name),
                    ProgramType::ParameterPointer(value_type),
                ))
            }
            _ => Err("only reference-backed Rust places can be borrowed or stored".into()),
        }
    }
    fn place_type(&mut self, e: &E) -> Result<ProgramType, String> {
        match e {
            E::Index { slice, .. } => Ok(self.indexed_parts(slice)?.2),
            E::Field { record, field, .. } => self
                .fields
                .get(&(record.as_str(), field.as_str()))
                .map(|(_, t)| *t)
                .ok_or("unknown Rust field type".into()),
            E::Deref { value_type, .. } => Ok(scalar_type(value_type)?.to_kernel_type()),
            _ => Err("unsupported Rust memory place type".into()),
        }
    }
    /// `e` as a branch's or loop's condition ([`branch_condition`]).
    fn condition(&mut self, e: &E) -> Result<ProgramExpression, String> {
        self.expr(e).map(branch_condition)
    }

    fn expr(&mut self, e: &E) -> Result<ProgramExpression, String> {
        match e {
            E::SharedArrayHasNext { iterator } => self.shared_array_has_next(iterator),
            E::RangeHasNext { iterator } => self.range_has_next(iterator),
            E::SharedArrayOptionTag { option }
                if self.library_slice_options.contains_key(option) =>
            {
                Ok(ProgramExpression::EnumIs {
                    value: Box::new(crate::kernel::program_expression::variable(option)),
                    variant: "Some".into(),
                })
            }
            E::SharedArrayOptionTag { option } => {
                if !self.shared_array_options.contains_key(option) {
                    return Err("unknown shared iterator Option".into());
                }
                Ok(crate::kernel::program_expression::variable(format!(
                    "{option}_some"
                )))
            }
            E::SharedArrayOptionElement { .. } => {
                Err("shared Option payload requires checked preparation".into())
            }
            E::EnumerateOptionIndex { .. } => {
                Err("enumerated Option index requires checked preparation".into())
            }
            E::ChunkHasNext { iterator } => self.chunk_has_next(iterator),
            E::ChunkOptionTag { option } => {
                if !self.chunk_options.contains(option) {
                    return Err("unknown chunk Option".into());
                }
                if library_iterators() {
                    return Ok(ProgramExpression::EnumIs {
                        value: Box::new(crate::kernel::program_expression::variable(option)),
                        variant: "Some".into(),
                    });
                }
                Ok(crate::kernel::program_expression::variable(format!(
                    "{option}_some"
                )))
            }
            E::ChunkOptionSlice { .. } | E::ChunkRemainder { .. } | E::ArrayToSlice { .. } => {
                Err("Rust slices require pointer-plus-length preparation".into())
            }
            E::Array { .. } | E::Repeat { .. } => {
                Err("array values require whole-array assignment".into())
            }
            E::Integer { value } => Ok(crate::kernel::program_expression::int32_literal(
                *value as u32,
            )),
            E::UsizeInteger { value } => {
                Ok(crate::kernel::program_expression::uint64_literal(*value))
            }
            E::EnumConstruct {
                name,
                variant,
                fields,
            } => {
                let enum_type = EnumTypes::get(name)?;
                let declared = enum_type
                    .algebraic_type()
                    .variants
                    .iter()
                    .find(|declared| declared.name == *variant)
                    .map(|declared| declared.fields.clone())
                    .ok_or_else(|| format!("unknown variant `{variant}` of a Rust enum"))?;
                // A field is converted to its declared type as an assignment
                // is: a `bool` operand is an `int` until it is stored.
                let fields = fields
                    .iter()
                    .zip(&declared)
                    .map(|(field, declared)| {
                        let value = self.expr(field)?;
                        Ok(match declared {
                            AlgebraicValueType::Program(interface_type) => {
                                crate::kernel::program_expression::cast(value, *interface_type)
                            }
                            _ => value,
                        })
                    })
                    .collect::<Result<_, String>>()?;
                Ok(ProgramExpression::EnumConstruct {
                    enum_type,
                    variant: variant.clone(),
                    fields,
                })
            }
            E::EnumField {
                base,
                variant,
                index,
                ..
            } => Ok(ProgramExpression::EnumField {
                value: Box::new(self.expr(base)?),
                variant: variant.clone(),
                index: *index,
            }),
            E::SliceLength { slice } => Ok(self.indexed_parts(slice)?.1),
            E::Index { .. } => Err("indexed Rust places require checked preparation".into()),
            E::UnsignedInteger { value, value_type } => match value_type {
                Type::U8 => Ok(crate::kernel::program_expression::uint8_literal(
                    u8::try_from(*value).map_err(|_| "Rust u8 literal out of range")?,
                )),
                Type::U16 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        u16::try_from(*value).map_err(|_| "Rust u16 literal out of range")? as u32,
                    ),
                    ProgramType::UInt16,
                )),
                Type::U32 => Ok(crate::kernel::program_expression::uint32_literal(
                    u32::try_from(*value).map_err(|_| "Rust u32 literal out of range")?,
                )),
                Type::U64 | Type::Usize => {
                    Ok(crate::kernel::program_expression::uint64_literal(*value))
                }
                _ => Err("unsigned literal needs an unsigned Rust type".into()),
            },
            E::SignedInteger { value, value_type } => match value_type {
                Type::I8 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        i8::try_from(*value).map_err(|_| "Rust i8 literal out of range")? as i32
                            as u32,
                    ),
                    ProgramType::Int8,
                )),
                Type::I16 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        i16::try_from(*value).map_err(|_| "Rust i16 literal out of range")? as i32
                            as u32,
                    ),
                    ProgramType::Int16,
                )),
                Type::I32 => Ok(crate::kernel::program_expression::int32_literal(
                    i32::try_from(*value).map_err(|_| "Rust i32 literal out of range")? as u32,
                )),
                Type::I64 | Type::Isize => {
                    Ok(crate::kernel::program_expression::int64_literal(*value))
                }
                _ => Err("signed literal needs a signed Rust type".into()),
            },
            E::Boolean { value } => Ok(crate::kernel::program_expression::int32_literal(
                u32::from(*value),
            )),
            E::NoneBox => Ok(crate::kernel::program_expression::cast(
                crate::kernel::program_expression::int32_literal(0),
                ProgramType::Int32Pointer,
            )),
            E::IntegerFrom {
                value,
                source_type,
                value_type,
            } => {
                let value = self.expr(value)?;
                integer_from(value, source_type, value_type)
            }
            E::Local { name } if self.memory_values.contains_key(name) => {
                let value_type = self.memory_values[name];
                Ok(crate::kernel::program_expression::typed_load(
                    self.address(e)?,
                    value_type,
                ))
            }
            E::Local { name } => {
                if !self.locals.contains(name) {
                    return Err(format!("unknown Rust local `{name}`"));
                }
                Ok(crate::kernel::program_expression::variable(name))
            }
            E::Not { value } => Ok(crate::kernel::program_expression::bool_value(
                crate::kernel::program_expression::not(self.expr(value)?),
            )),
            E::Borrow { place, value_type } => {
                if let E::Field { record, field, .. } = place.as_ref()
                    && self
                        .fields
                        .get(&(record.as_str(), field.as_str()))
                        .is_some_and(|(_, ty)| array_field_parts(*ty).is_some())
                    && matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                Ok(reference_view(
                    self.address(place)?,
                    scalar_type(value_type)?.to_kernel_type(),
                    false,
                    false,
                ))
            }
            E::Cast { value, value_type } => Ok(rust_scalar_cast(
                self.expr(value)?,
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::BitwiseNot { value, value_type } => Ok(rust_bitwise_not(
                self.expr(value)?,
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::Deref { .. } | E::Field { .. } => {
                if array_field_parts(self.place_type(e)?).is_some() {
                    return Err("array fields must be borrowed or indexed; owned field copies are unsupported".into());
                }
                let pointer = self.address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok(crate::kernel::program_expression::typed_load_with_source(
                    pointer,
                    self.place_type(e)?,
                    Some(LoadSourceId {
                        owner: LoadSourceOwnerId {
                            source_unit: self.source.into(),
                            function: self.function.into(),
                        },
                        occurrence,
                        reference_access: self
                            .reference_source(e, ReferenceAccessKind::Read)
                            .map(std::sync::Arc::new),
                    }),
                ))
            }
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } => {
                let mut l = self.expr(left)?;
                let r = self.expr(right)?;
                // A Rust comparison of two 8- or 16-bit values is native
                // at their type (`design/machine-integers.md`, Decisions
                // 2026-11-01): its operands keep their width, and the `bool`
                // value below reads the comparison at it.
                let narrow = matches!(left_type, Type::U8 | Type::U16 | Type::I8 | Type::I16);
                let narrow_comparison =
                    narrow && matches!(operator.as_str(), "eq" | "ne" | "lt" | "le" | "gt" | "ge");
                // Rust `+ - * & | ^ <<` on 8- or 16-bit values are the
                // operators of that type (decision G4): native nodes over the
                // operands as written. A checked operator's overflow panic is
                // its own assertion (`prepared_expr`). A native shift's count
                // is a 32-bit word; a count of another width keeps the
                // promoted shift.
                let narrow_native = narrow
                    && (matches!(
                        operator.as_str(),
                        "add" | "sub" | "mul" | "bit_and" | "bit_or" | "bit_xor"
                    ) || (operator == "shl" && right_type.integer_bits() == Some(32)));
                // Keep the RHS at its source width. The shared shift evaluator
                // checks signed/nonnegative and full-width upper bounds before
                // forming its word-sized shift term. Narrowing here would lose
                // the exact relation to Rust's already checked count.
                if narrow && !narrow_comparison && !narrow_native {
                    // Rust narrow `/ % >>` are still a 32-bit operation and
                    // a cast back (decision G4).
                    crate::kernel::machine_integer::format_audit::record(
                        crate::kernel::machine_integer::format_audit::WordIdentity::PromotedNarrowArithmetic,
                        std::panic::Location::caller(),
                    );
                }
                if narrow_comparison || narrow_native {
                } else if matches!(left_type, Type::U8 | Type::U16) {
                    // Narrow unsigned remainder fits in signed int, matching
                    // the promotion used by its contract expression. Other
                    // operations keep unsigned words (notably u16 multiply).
                    l = crate::kernel::program_expression::cast(
                        l,
                        if operator == "rem" {
                            ProgramType::Int32
                        } else {
                            ProgramType::UInt32
                        },
                    );
                } else if left_type.is_signed_integer() && operator == "shl" {
                    // A signed left shift wraps in Rust and may be undefined
                    // in C: shift the bits as an unsigned word of at least
                    // the operand's width, then reinterpret them at the
                    // operand's width below.
                    l = crate::kernel::program_expression::cast(
                        l,
                        if left_type.integer_bits() == Some(64) {
                            ProgramType::UInt64
                        } else {
                            ProgramType::UInt32
                        },
                    );
                } else if matches!(left_type, Type::I8 | Type::I16) {
                    l = crate::kernel::program_expression::cast(l, ProgramType::Int32);
                }
                let result = match operator.as_str() {
                    "add" => crate::kernel::program_expression::add(l, r),
                    "sub" => crate::kernel::program_expression::subtract(l, r),
                    "mul" => crate::kernel::program_expression::multiply(l, r),
                    "div" => crate::kernel::program_expression::divide(l, r),
                    "rem" => crate::kernel::program_expression::remainder(l, r),
                    "shl" => crate::kernel::program_expression::shift_left(l, r),
                    "shr" => crate::kernel::program_expression::shift_right(l, r),
                    "bit_and" => crate::kernel::program_expression::bitwise_and(l, r),
                    "bit_or" => crate::kernel::program_expression::bitwise_or(l, r),
                    "bit_xor" => crate::kernel::program_expression::bitwise_xor(l, r),
                    "eq" => crate::kernel::program_expression::equal(l, r),
                    "ne" => crate::kernel::program_expression::not_equal(l, r),
                    "lt" => crate::kernel::program_expression::less_than(l, r),
                    "le" => crate::kernel::program_expression::less_equal(l, r),
                    "gt" => crate::kernel::program_expression::greater_than(l, r),
                    "ge" => crate::kernel::program_expression::greater_equal(l, r),
                    "and" => crate::kernel::program_expression::and(l, r),
                    "or" => crate::kernel::program_expression::or(l, r),
                    _ => return Err("unsupported Rust operator in artifact".into()),
                };
                if matches!(
                    operator.as_str(),
                    "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
                ) {
                    // A Rust comparison or connective is a `bool` value: the
                    // condition itself, with no path split (Stage 5, D5).
                    Ok(crate::kernel::program_expression::bool_value(result))
                } else if narrow_native {
                    Ok(crate::kernel::program_expression::narrow_arithmetic(
                        result,
                        scalar_type(left_type)?.to_kernel_type(),
                    ))
                } else if narrow && matches!(operator.as_str(), "div" | "rem") {
                    // Checked narrow arithmetic cannot discard bits. Its range
                    // obligation permits an exact coercion; only casts,
                    // bitwise results and shifts need explicit truncation.
                    // Convert from the operation's promoted type: `int32` for
                    // signed arithmetic and narrow unsigned remainder,
                    // `uint32` for the other unsigned operations.
                    let computed = if matches!(left_type, Type::U8 | Type::U16) {
                        result
                    } else {
                        crate::kernel::program_expression::cast(result, ProgramType::Int32)
                    };
                    Ok(crate::kernel::program_expression::cast(
                        computed,
                        scalar_type(left_type)?.to_kernel_type(),
                    ))
                } else {
                    Ok(rust_scalar_cast(
                        result,
                        scalar_type(left_type)?.to_kernel_type(),
                    ))
                }
            }
            E::Call { .. } => Err("nested Rust calls outside statement lowering".into()),
            E::ClosureInstance { .. } => {
                Err("Rust closure instance outside an assignment to a local".into())
            }
            E::FunctionAddress {
                function,
                value_type,
            } => {
                let target = self
                    .functions
                    .get(function.as_str())
                    .ok_or("Rust function pointer to an unknown function")?;
                let Type::FnPointer { parameters, result } = value_type else {
                    return Err("Rust function address requires a function-pointer type".into());
                };
                if target.return_type != **result
                    || target.parameters.len() != parameters.len()
                    || target
                        .parameters
                        .iter()
                        .zip(parameters)
                        .any(|(parameter, expected)| parameter.value_type != *expected)
                {
                    return Err(format!(
                        "Rust function address `{function}` does not have its function's type"
                    ));
                }
                Ok(crate::kernel::program_expression::function_address(
                    function,
                ))
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/languages/rust/lowering/tests.rs");
}
