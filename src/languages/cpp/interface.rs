//! Contract-facing metadata prepared by the C++ frontend alongside execution.
use super::{CppStatement, CppType, PreparedCppImport};
use crate::kernel::CFunction;
use crate::languages::PreparedExecution;
use crate::languages::c::syntax::{self, C0Type};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn prepare(
    import: &PreparedCppImport,
    function: &CFunction,
    reachable: &[CFunction],
) -> Result<PreparedExecution, String> {
    let mut layouts = BTreeMap::new();
    for record in &import.export().records {
        let fields = record
            .fields
            .iter()
            .map(|field| {
                crate::instrumentation::record_deterministic_work(1);
                let value_type = match &field.value_type {
                    CppType::Integer {
                        bits: 32,
                        signed: true,
                        is_const: false,
                        ..
                    } => C0Type::Int32,
                    CppType::Integer {
                        bits: 64,
                        signed: true,
                        is_const: false,
                        ..
                    } => C0Type::Int64,
                    CppType::Pointer { pointee }
                        if matches!(
                            pointee.as_ref(),
                            CppType::Integer {
                                bits: 32,
                                signed: true,
                                is_const: false,
                                ..
                            }
                        ) =>
                    {
                        C0Type::Int32Pointer
                    }
                    _ => {
                        return Err(format!(
                            "C++ record field `{}.{}` is outside the supported proof interface",
                            record.name, field.name
                        ));
                    }
                };
                Ok((
                    field.name.clone(),
                    value_type,
                    field.offset_bytes,
                    field.size_bytes,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let layout = syntax::C0StructLayout::from_explicit_fields(
            fields,
            record.size_bytes,
            record.alignment_bytes,
        )
        .map_err(|error| format!("invalid C++ record layout for `{}`: {error}", record.name))?;
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err(format!("duplicate C++ record name `{}`", record.name));
        }
    }
    let functions = std::iter::once(&import.export().function)
        .chain(&import.export().reachable_functions)
        .zip(std::iter::once(function).chain(reachable))
        .map(|(source, kernel)| {
            crate::instrumentation::record_deterministic_work(1);
            let mut locals = BTreeMap::new();
            let mut ambiguous = BTreeSet::new();
            let mut pending = vec![source.body.as_slice()];
            while let Some(body) = pending.pop() {
                for statement in body {
                    crate::instrumentation::record_deterministic_work(1);
                    match statement {
                        CppStatement::Declare { local, .. } => {
                            if let CppType::Record { name, .. } = &local.value_type {
                                if locals.get(&local.name).is_some_and(|known| known != name) {
                                    ambiguous.insert(local.name.clone());
                                }
                                locals.insert(local.name.clone(), name.clone());
                            }
                        }
                        CppStatement::Scope { body, .. } => pending.push(body),
                        CppStatement::If {
                            then_branch,
                            else_branch,
                            ..
                        } => {
                            pending.push(then_branch);
                            pending.push(else_branch);
                        }
                        CppStatement::TryCatchInt32 {
                            try_body, handler, ..
                        } => {
                            pending.push(try_body);
                            pending.push(handler);
                        }
                        _ => {}
                    }
                }
            }
            for name in ambiguous {
                locals.remove(&name);
            }
            Ok(function_interface(source, kernel)?.with_local_struct_values(locals))
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(PreparedExecution { functions, layouts })
}

/// Builds the proof-facing signature for the supported C++ profile from Clang's
/// typed declaration. The body deliberately remains absent here: executable
/// semantics come from `lower_import`, never from reconstructing C++ as C.
fn function_interface(
    source: &super::CppFunction,
    lowered: &crate::kernel::CFunction,
) -> Result<syntax::C0Function, String> {
    let return_type = match source.return_type {
        CppType::Void => C0Type::Void,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            ..
        } => C0Type::Int32,
        CppType::Integer {
            bits: 64,
            signed: true,
            is_const: false,
            ..
        } => C0Type::Int64,
        CppType::Integer {
            bits: 32,
            signed: false,
            is_const: false,
            ..
        } => C0Type::UInt32,
        CppType::Integer {
            bits: 64,
            signed: false,
            is_const: false,
            ..
        } => C0Type::UInt64,
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => C0Type::Bool,
        _ => {
            return Err(format!(
                "C++ declaration `{}` has an unsupported return type",
                source.declaration_id
            ));
        }
    };
    let parameters = source
        .parameters
        .iter()
        .map(|parameter| {
            crate::instrumentation::record_deterministic_work(1);
            match &parameter.value_type {
            CppType::Integer { bits, signed, is_const: false, .. } if *bits == 32 || *bits == 64 => Ok(syntax::C0Parameter::new(match (*bits, *signed) { (32,true) => C0Type::Int32, (64,true) => C0Type::Int64, (32,false) => C0Type::UInt32, _ => C0Type::UInt64 }, parameter.name.clone(), None)),
            CppType::Boolean {
                bits: 8,
                is_const: false,
            } => Ok(syntax::C0Parameter::new(
                C0Type::Bool,
                parameter.name.clone(),
                None,
            )),
            CppType::LvalueReference { pointee }
                if matches!(
                    pointee.as_ref(),
                    CppType::Integer {
                        bits: 32,
                        signed: true,
                        ..
                    }
                ) =>
            {
                let CppType::Integer { is_const, .. } = pointee.as_ref()
                else {
                    unreachable!("guarded by the supported integer-reference pattern")
                };
                Ok(syntax::C0Parameter::new(
                    C0Type::Int32Pointer,
                    parameter.name.clone(),
                    None,
                )
                .with_pointee_constant(*is_const))
            }
            CppType::LvalueReference { pointee }
                if matches!(
                    pointee.as_ref(),
                    CppType::Integer {
                        bits: 64,
                        signed: true,
                        is_const: true,
                        ..
                    }
                ) =>
            {
                Ok(syntax::C0Parameter::new(
                    C0Type::Int64Pointer,
                    parameter.name.clone(),
                    None,
                )
                .with_pointee_constant(true))
            }
            CppType::LvalueReference { pointee } => {
                let CppType::Record { name, is_const, .. } = pointee.as_ref() else {
                    return Err(format!(
                        "C++ declaration `{}` parameter `{}` has an unsupported reference pointee",
                        source.declaration_id, parameter.name
                    ));
                };
                Ok(syntax::C0Parameter::new(
                    C0Type::Int32Pointer,
                    parameter.name.clone(),
                    Some(name.clone()),
                ).with_pointee_constant(*is_const))
            }
            CppType::Pointer { pointee }
                if matches!(
                    pointee.as_ref(),
                    CppType::Integer {
                        bits: 32,
                        signed: true,
                        is_const: false,
                        ..
                    }
                ) =>
            {
                Ok(syntax::C0Parameter::new(
                    C0Type::Int32Pointer,
                    parameter.name.clone(),
                    None,
                ))
            }
            _ => Err(format!(
                "C++ declaration `{}` parameter `{}` is outside the supported bool/reference/pointer/record interface",
                source.declaration_id, parameter.name
            )),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(
        syntax::C0Function::external(return_type, lowered.name().to_owned(), parameters)
            .with_prelowered_kernel_function(lowered.clone()),
    )
}
