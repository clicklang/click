//! Contract-facing metadata prepared by the C++ frontend alongside execution.
use super::scalar::{Scalar, ScalarKind};
use super::{CppStatement, CppType, PreparedCppImport};
use crate::kernel::CFunction;
use crate::languages::PreparedExecution;
use crate::languages::c::syntax::{self, C0Type, LongRank};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn prepare(
    import: &PreparedCppImport,
    selected: &[CFunction],
    reachable: &[CFunction],
    layouts: BTreeMap<String, syntax::C0StructLayout>,
    library_contracts: String,
    object_coercions: &BTreeSet<(String, String)>,
) -> Result<PreparedExecution, String> {
    let mut functions = prepare_functions(import, selected, reachable, &layouts)?;
    // Where a reference to a derived class becomes a reference to its
    // polymorphic base, the importer places a pack before the call and an
    // unpack after it, each taking the derived class's address. Their
    // contracts are the sidecar's; without one, each moves nothing.
    for (derived, base) in object_coercions {
        let layout = layouts
            .get(derived)
            .ok_or("C++ base conversion's derived class has no checked layout")?;
        for name in [
            crate::languages::cpp::names::object_pack_name(derived, base),
            crate::languages::cpp::names::object_unpack_name(derived, base),
        ] {
            crate::instrumentation::record_deterministic_work(1);
            let object = syntax::C0Parameter::new(
                C0Type::Int32Pointer,
                "object".to_string(),
                Some(derived.clone()),
            )
            .with_pointee_struct_layout(derived.clone(), layout.clone())
            .with_pointee_constant(true);
            functions.push(syntax::C0Function::external(
                C0Type::Void,
                name,
                vec![object],
            ));
        }
    }
    let record_spellings = import
        .export()
        .records
        .iter()
        .flat_map(|record| {
            // A head's qualifier writes the record's own segment,
            // `Stored<long long>::Read`; a type writes its path,
            // `std::span<int>`.
            [record.path.last().cloned(), Some(record.path.join("::"))]
                .into_iter()
                .flatten()
                .filter(|spelling| spelling != &record.name)
                .map(|spelling| (spelling, record.name.clone()))
        })
        .collect();
    Ok(PreparedExecution {
        functions,
        layouts,
        library_contracts,
        record_spellings,
    })
}

/// Materialize checked nominal layouts once for execution and proof metadata.
pub(super) fn prepare_layouts(
    import: &PreparedCppImport,
) -> Result<BTreeMap<String, syntax::C0StructLayout>, String> {
    let mut layouts = BTreeMap::new();
    let records = import
        .export()
        .records
        .iter()
        .map(|record| (record.declaration_id.clone(), record))
        .collect();
    let mut leaf_counts = BTreeMap::new();
    let mut total_leaves = 0usize;
    for record in super::schema::record_layout_order(&records)? {
        let mut leaves: usize = record.base.as_ref().map_or(0, |base| {
            let CppType::Record { name, .. } = &base.value_type else {
                unreachable!("validated nominal base")
            };
            leaf_counts[name.as_str()]
        });
        for field in &record.fields {
            crate::instrumentation::record_deterministic_work(1);
            leaves = leaves.saturating_add(match &field.value_type {
                CppType::Record { name, .. } => leaf_counts[name.as_str()],
                _ => 1,
            });
        }
        total_leaves = total_leaves.saturating_add(leaves);
        super::budget::limit(
            "materialized record layout leaves",
            total_leaves,
            super::budget::MAX_RECORD_LAYOUT_LEAVES,
        )?;
        leaf_counts.insert(record.name.as_str(), leaves);
        let mut constant_pointees = Vec::new();
        let mut fields = record
            .fields
            .iter()
            .map(|field| {
                crate::instrumentation::record_deterministic_work(1);
                let mut struct_name = None;
                let value_type = match &field.value_type {
                    value
                        if Scalar::mutable_kind(value).is_some_and(|kind| {
                            matches!(
                                kind,
                                ScalarKind::UInt8
                                    | ScalarKind::Int32
                                    | ScalarKind::UInt32
                                    | ScalarKind::Int64
                                    | ScalarKind::UInt64
                            )
                        }) =>
                    {
                        Scalar::mutable_kind(value).unwrap().proof_type()
                    }
                    CppType::Pointer { pointee }
                        if Scalar::pointer_element(pointee, true).is_some() =>
                    {
                        let element = Scalar::pointer_element(pointee, true).unwrap();
                        if element.is_const {
                            constant_pointees.push(field.name.clone());
                        }
                        element.kind.pointer_proof_type().unwrap()
                    }
                    CppType::Record {
                        name,
                        is_const: false,
                        ..
                    } => {
                        struct_name = Some(name.clone());
                        C0Type::Int32 // C's nominal embedded-record placeholder.
                    }
                    CppType::Array { element, length } => {
                        match Scalar::pointer_element(element, false).map(|scalar| scalar.kind) {
                            Some(ScalarKind::Int32) => C0Type::Int32Array(*length),
                            Some(ScalarKind::UInt32) => C0Type::UInt32Array(*length),
                            Some(ScalarKind::UInt8) => C0Type::UInt8Array(*length),
                            _ => {
                                return Err(format!(
                                    "C++ record field `{}.{}` has an unsupported array element",
                                    record.name, field.name
                                ));
                            }
                        }
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
                    struct_name,
                    field.offset_bytes,
                    field.size_bytes,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        if let Some(base) = &record.base {
            crate::instrumentation::record_deterministic_work(1);
            let CppType::Record { name, .. } = &base.value_type else {
                unreachable!("validated nominal base")
            };
            fields.insert(
                0,
                (
                    "base".into(),
                    C0Type::Int32,
                    Some(name.clone()),
                    base.offset_bytes,
                    base.size_bytes,
                ),
            );
        }
        let mut layout = syntax::C0StructLayout::from_explicit_fields_with_structs(
            fields,
            record.size_bytes,
            record.alignment_bytes,
            &layouts,
        )
        .map_err(|error| format!("invalid C++ record layout for `{}`: {error}", record.name))?;
        for name in &constant_pointees {
            layout.mark_pointee_constant(name)?;
        }
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err(format!("duplicate C++ record name `{}`", record.name));
        }
    }
    Ok(layouts)
}

fn prepare_functions(
    import: &PreparedCppImport,
    selected: &[CFunction],
    reachable: &[CFunction],
    layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Result<Vec<syntax::C0Function>, String> {
    let observers = super::schema::observer_callees(import);
    // An override's interface is the virtual method it overrides, which a
    // call through that method assumes of it.
    let names = import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .zip(selected.iter().chain(reachable))
        .map(|(source, kernel)| (source.declaration_id.as_str(), kernel.name()))
        .collect::<BTreeMap<_, _>>();
    import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .zip(selected.iter().chain(reachable))
        .map(|(source, kernel)| {
            crate::instrumentation::record_deterministic_work(1);
            let mut locals = BTreeMap::new();
            let mut references = BTreeSet::new();
            let mut objects = BTreeSet::new();
            let mut ambiguous = BTreeSet::new();
            let mut pending = vec![source.body.as_slice()];
            while let Some(body) = pending.pop() {
                for statement in body {
                    crate::instrumentation::record_deterministic_work(1);
                    match statement {
                        CppStatement::Declare { local, .. } => {
                            // A name declared both as a reference and as
                            // an object, in two scopes, is read as written.
                            if matches!(local.value_type, CppType::LvalueReference { .. }) {
                                references.insert(local.name.clone());
                            } else {
                                objects.insert(local.name.clone());
                            }
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
            let interface = source
                .virtual_method
                .iter()
                .flat_map(|method| &method.overrides)
                .map(|overridden| names[overridden.declaration_id.as_str()].to_string())
                .next();
            Ok(function_interface(source, kernel, layouts)?
                .with_trait_interface(interface)
                .with_read_only_contract(observers.contains(&source.declaration_id))
                .with_local_struct_values(locals)
                .with_local_references(references.difference(&objects).cloned().collect()))
        })
        .collect::<Result<Vec<_>, String>>()
}

/// Builds the proof-facing signature for the supported C++ profile from Clang's
/// typed declaration. The body deliberately remains absent here: executable
/// semantics come from `lower_import`, never from reconstructing C++ as C.
fn function_interface(
    source: &super::CppFunction,
    lowered: &crate::kernel::CFunction,
    layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Result<syntax::C0Function, String> {
    let return_reference = matches!(source.return_type, CppType::LvalueReference { .. });
    let return_element = super::scalar::reference_element(&source.return_type);
    let return_constant = super::scalar::returns_constant_element(&source.return_type);
    let return_type = if source.return_type == CppType::Void {
        C0Type::Void
    } else if let Some(element) = return_element {
        element
            .kind
            .pointer_proof_type()
            .ok_or("unsupported native reference return interface")?
    } else if matches!(source.return_type, CppType::Record { .. }) || return_reference {
        C0Type::Int32Pointer
    } else if let CppType::Pointer { pointee } = &source.return_type {
        Scalar::pointer_element(pointee, true)
            .and_then(|scalar| scalar.kind.pointer_proof_type())
            .ok_or("unsupported native pointer return interface")?
    } else {
        Scalar::mutable_kind(&source.return_type)
            .map(ScalarKind::proof_type)
            .ok_or_else(|| {
                format!(
                    "C++ declaration `{}` has an unsupported return type",
                    source.declaration_id
                )
            })?
    };
    let parameters = source
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            crate::instrumentation::record_deterministic_work(1);
            let is_reference = super::lowering::is_reference_parameter(index, parameter);
            let carried_name = if super::lowering::is_receiver(index, parameter) {
                super::lowering::RECEIVER_NAME.to_string()
            } else if is_reference {
                super::lowering::reference_carrier_name(&parameter.name)
            } else {
                parameter.name.clone()
            };
            if let Some(kind) = Scalar::mutable_kind(&parameter.value_type) {
                return Ok(syntax::C0Parameter::new(kind.proof_type(), carried_name.clone(), None));
            }
            match &parameter.value_type {
            CppType::Record { name, is_const: false, .. } => {
                let layout = layouts.get(name).ok_or("C++ record parameter has no checked layout")?;
                Ok(syntax::C0Parameter::new(C0Type::UInt8Pointer, carried_name.clone(), None)
                    .with_struct_value(name.clone(), layout.clone()))
            }
            reference @ CppType::LvalueReference { .. }
                if super::scalar::reference_element(reference).is_some() =>
            {
                let element = super::scalar::reference_element(reference).unwrap();
                Ok(syntax::C0Parameter::new(
                    element
                        .kind
                        .pointer_proof_type()
                        .ok_or("unsupported native reference parameter interface")?,
                    carried_name.clone(),
                    None,
                )
                .with_pointee_constant(element.is_const)
                .with_reference(is_reference))
            }
            CppType::LvalueReference { pointee }
                if Scalar::is(pointee, ScalarKind::Int64, true) =>
            {
                Ok(syntax::C0Parameter::new(
                    C0Type::Int64Pointer(LongRank::Long),
                    carried_name.clone(),
                    None,
                )
                .with_pointee_constant(true)
                .with_reference(is_reference))
            }
            CppType::LvalueReference { pointee } => {
                let CppType::Record { name, is_const, .. } = pointee.as_ref() else {
                    return Err(format!(
                        "C++ declaration `{}` parameter `{}` has an unsupported reference pointee",
                        source.declaration_id, parameter.name
                    ));
                };
                let carrier = syntax::C0Parameter::new(
                    C0Type::Int32Pointer,
                    carried_name.clone(),
                    Some(name.clone()),
                );
                // The record's layout is what lets a diagnostic name a field
                // of the referent, `c.first`, where it would print a cell.
                let carrier = match layouts.get(name) {
                    Some(layout) => carrier.with_pointee_struct_layout(name.clone(), layout.clone()),
                    None => carrier,
                };
                Ok(carrier
                    .with_pointee_constant(*is_const)
                    .with_reference(is_reference))
            }
            CppType::FunctionPointer { .. } => Ok(syntax::C0Parameter::function_pointer(
                carried_name.clone(),
                function_pointer_signature(&parameter.value_type)?,
            )),
            CppType::Pointer { pointee } if Scalar::pointer_element(pointee, false).is_some() =>
            {
                Ok(syntax::C0Parameter::new(
                    Scalar::pointer_element(pointee, false).unwrap().kind.pointer_proof_type().unwrap(),
                    carried_name.clone(),
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
    let mut interface =
        syntax::C0Function::external(return_type, lowered.name().to_owned(), parameters)
            .with_return_reference(return_reference)
            .with_return_pointee_constant(return_constant);
    // An axiom keeps no body: its calls are checked against a contract.
    // A pure virtual method is only its interface.
    if source.axiom.is_none() && !source.is_pure_virtual() {
        interface = interface.with_prelowered_kernel_function(lowered.clone());
    }
    // A lambda's leading parameters are its captures, which a sidecar head
    // does not write; its contract reads them by name.
    interface = interface.with_closure_captures(source.closure_captures);
    if let CppType::Record { name, .. } = &source.return_type {
        let layout = layouts
            .get(name)
            .ok_or("C++ record return has no checked layout")?;
        interface = interface
            .with_struct_return(name.clone(), layout.clone())
            .with_aggregate_return_mode(lowered.contract_interface().aggregate_return_mode());
    }
    Ok(interface)
}

/// The signature of a function-pointer type in proof types, as a C
/// function-pointer declarator in a sidecar head spells it.
pub(super) fn function_pointer_signature(
    value_type: &CppType,
) -> Result<syntax::C0FunctionPointerSignature, String> {
    let CppType::FunctionPointer {
        return_type,
        parameters,
        ..
    } = value_type
    else {
        return Err("C++ function-pointer signature requires a function-pointer type".into());
    };
    let proof_type = |value_type: &CppType| match value_type {
        CppType::Void => Some(C0Type::Void),
        CppType::Pointer { pointee } => Scalar::pointer_element(pointee, false)
            .and_then(|element| element.kind.pointer_proof_type()),
        _ => Scalar::mutable_kind(value_type).map(ScalarKind::proof_type),
    };
    let unsupported = || "C++ function-pointer type is outside the proof interface".to_string();
    let return_type = proof_type(return_type).ok_or_else(unsupported)?;
    let parameters = parameters
        .iter()
        .map(|parameter| {
            crate::instrumentation::record_deterministic_work(1);
            proof_type(parameter)
                .filter(|c_type| *c_type != C0Type::Void)
                .map(|c_type| syntax::C0FunctionPointerParameter::new(c_type, None, false))
                .ok_or_else(unsupported)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(syntax::C0FunctionPointerSignature::new(
        return_type,
        None,
        parameters,
        false,
    ))
}
