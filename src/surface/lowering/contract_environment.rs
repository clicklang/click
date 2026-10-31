//! The environment a contract or proof-side expression is read in: the
//! values and array references in scope at a state, the snapshot a selector
//! names, and the pointer-offset spelling contract-lowered ranges share with
//! kernel execution. Nothing here evaluates an expression; that is the
//! kernel's, through the elaborated spec form.

use super::*;
use crate::surface::diagnostics::describe_program_point_ref;

pub(in crate::surface) fn array_refs_with_memory(
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
) -> ClickArrayRefs {
    array_refs
        .iter()
        .map(|(name, array_ref)| {
            (
                name.clone(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: array_ref.pointer.clone(),
                    element_type: array_ref.element_type,
                },
            )
        })
        .collect()
}

pub(in crate::surface) fn contract_environment_at_state(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
) -> (BTreeMap<String, CValue>, ClickArrayRefs) {
    let mut values = parameter_values.clone();
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );

    let mut state_array_refs = array_refs_with_memory(array_refs, state.memory());
    // A parameter's array reference is read through the variable, exactly as
    // its value is above. `array_refs` was built from the caller's arguments,
    // so after the body assigns a pointer parameter it still holds the entry
    // pointer while `values` holds the current one; a pure function or theorem
    // argument naming that parameter then read two different pointers under
    // one name.
    for (name, value) in state.locals().object_values() {
        if let CValue::Pointer(pointer) = value
            && let Some(array_ref) = state_array_refs.get_mut(name)
        {
            array_ref.pointer = pointer.pointer().clone();
        }
    }
    for (name, value, element_type) in state.locals().array_object_values() {
        let CValue::Pointer(pointer) = value.clone() else {
            unreachable!("local array values are pointers")
        };
        // File-scope arrays remain in the state even when a parameter hides
        // their name. They must not replace that parameter's current value.
        if pointer.block.is_global_block() && parameter_values.contains_key(name) {
            continue;
        }
        values.insert(name.to_string(), value);
        state_array_refs.insert(
            name.to_string(),
            ClickArrayRef {
                memory: state.memory().clone(),
                pointer: pointer.pointer().clone(),
                element_type,
            },
        );
    }
    (values, state_array_refs)
}

/// [`contract_environment_at_state`] restricted to `names`: the same entry for
/// each named parameter or local, read by indexed lookups, so building it
/// costs the names a proposition mentions rather than every parameter and
/// local in scope. Without a parameter index, every parameter is read.
pub(in crate::surface) fn contract_environment_for_names(
    parameter_binding: ParameterBinding<'_>,
    names: &BTreeSet<String>,
    state: &CState,
) -> Result<(BTreeMap<String, CValue>, ClickArrayRefs), ClickError> {
    let mut values = parameter_values_named(parameter_binding, names)?;
    let mut array_refs = array_refs_for_values(parameter_binding, &values, state.memory());
    for name in names {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = state.locals().get(name) {
            // As in `contract_environment_at_state`, a parameter's array
            // reference follows the variable's current pointer.
            if let CValue::Pointer(pointer) = value
                && let Some(array_ref) = array_refs.get_mut(name)
            {
                array_ref.pointer = pointer.pointer().clone();
            }
            values.insert(name.clone(), value.clone());
        } else if let Some((value, element_type)) = state.locals().array_object_value(name) {
            let CValue::Pointer(pointer) = &value else {
                unreachable!("local array values are pointers")
            };
            if pointer.block.is_global_block() && values.contains_key(name) {
                continue;
            }
            array_refs.insert(
                name.clone(),
                ClickArrayRef {
                    memory: state.memory().clone(),
                    pointer: pointer.pointer().clone(),
                    element_type,
                },
            );
            values.insert(name.clone(), value);
        }
    }
    Ok((values, array_refs))
}

pub(in crate::surface) fn selected_snapshot_state<'a>(
    selector: &SnapshotSelector,
    function_entry_state: &'a CState,
    recorded_snapshots: &'a RecordedSnapshots,
) -> Result<&'a CState, String> {
    match selector {
        SnapshotSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        SnapshotSelector::Mark(name) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )
        }),
        SnapshotSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Region(_)
                | CodeRegionRef::Loop(_)
                | CodeRegionRef::Label(_),
            ..
        }) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "no state snapshot was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                describe_program_point_ref(point)
            )
        }),
        SnapshotSelector::ProgramPoint(
            point @ ProgramPointRef {
                region: CodeRegionRef::Path(_),
                ..
            },
        ) => {
            let region = recorded_snapshots.source_point(point)?;
            recorded_snapshots.get(selector).ok_or_else(|| {
                format!(
                    "no state snapshot was recorded for `{}`, which is `{}`; run `step()` across that statement before using it in `at(...)`",
                    describe_program_point_ref(point),
                    crate::surface::diagnostics::describe_program_point_ref_as_recorded(&region)
                )
            })
        }
        SnapshotSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(in crate::surface) fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<CType> {
    match expression {
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
            array_refs.get(name).map(|array_ref| array_ref.element_type)
        }
        ContractExpression::Old(expression) => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::At { expression, .. } => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::Add(left, right) => contract_array_ref_element_type(array_refs, left)
            .or_else(|| contract_array_ref_element_type(array_refs, right)),
        ContractExpression::Subtract(left, _) => contract_array_ref_element_type(array_refs, left),
        _ => None,
    }
}

pub(in crate::surface) fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    match (value.numeric_value(), c_type) {
        (
            CValue::Int8(_),
            C0Type::Int8 | C0Type::Char(crate::languages::c::syntax::PlainChar::Signed),
        ) => true,
        (CValue::Int16(_), C0Type::Int16)
        | (CValue::Int32(_), C0Type::Int32)
        | (
            CValue::UInt8(_),
            C0Type::Char(crate::languages::c::syntax::PlainChar::Unsigned) | C0Type::UInt8,
        )
        | (CValue::UInt16(_), C0Type::UInt16)
        | (CValue::UInt32(_), C0Type::UInt32)
        | (CValue::Int64(_), C0Type::Int64(_))
        | (CValue::UInt64(_), C0Type::UInt64(_))
        | (CValue::Int128(_), C0Type::Int128)
        | (CValue::UInt128(_), C0Type::UInt128) => true,
        (CValue::Pointer(pointer), c_type) if c_type.is_pointer() => pointer
            .c_type()
            .pointer_types_compatible(c_type.to_kernel_type()),
        _ => false,
    }
}

/// The built-in allocation authority is byte-addressed independently of the
/// pointer type used by the C caller. Its public declaration keeps the
/// historical `int32*` spelling, but allocator contracts may name any
/// modeled data pointer (including pointer-to-pointer storage).
pub(in crate::surface) fn c_value_matches_allocation_pointer(value: &CValue) -> bool {
    matches!(
        value,
        CValue::Pointer(pointer) if pointer.c_type().pointee_type().is_some()
    )
}

#[cfg(test)]
pub(in crate::surface) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(in crate::surface) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    // A loaded index never enters a pointer offset as a `MemoryLoad` term:
    // its load variable stands in for it, so contract-side offsets use the
    // same terms kernel execution does. Names are content-addressed, so no
    // fact stream is needed here — the defining equation is emitted wherever
    // the kernel evaluates the same load.
    let mut discarded_facts = crate::kernel::ExecutionFacts::new();
    let elements = crate::kernel::canonicalized_offset_index_term(elements, &mut discarded_facts);
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

pub(in crate::surface) fn add_pointer_offset(
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn scale_int32_offset(
    value: Bitvector32Term,
    byte_width: i64,
) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn globals(unrelated: usize) -> CState {
        let arrays = std::iter::once("bytes".to_string())
            .chain((0..unrelated).map(|i| format!("other_{i}")))
            .map(|name| {
                crate::kernel::CGlobalArray::new_with_kernel_name(
                    &name,
                    &name,
                    CType::UInt8,
                    2,
                    vec![crate::kernel::uint8(0); 2],
                )
            })
            .collect();
        let function = crate::kernel::CFunction::new(
            CType::Void,
            "shadow",
            vec![],
            crate::kernel::CStatement::Skip,
        )
        .with_global_arrays(arrays);
        crate::kernel::c_function_entry_state(&CState::new(), &function, &[]).unwrap()
    }

    fn assert_bytes(
        values: &BTreeMap<String, CValue>,
        arrays: &ClickArrayRefs,
        value: &CValue,
        element_type: CType,
    ) {
        assert_eq!(values.get("bytes"), Some(value));
        let CValue::Pointer(pointer) = value else {
            unreachable!()
        };
        assert_eq!(arrays["bytes"].pointer, *pointer.pointer());
        assert_eq!(arrays["bytes"].element_type, element_type);
    }

    #[test]
    fn parameter_array_binding_hides_global_and_follows_reassignment() {
        let state = globals(0);
        let value = CValue::typed_pointer(
            Pointer {
                block: "parameter-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::Int32Pointer,
        );
        let parameters = [syntax::C0Parameter::new(
            C0Type::Int32Pointer,
            "bytes".into(),
            None,
        )];
        let arguments = [CExpression::Value(value.clone())];
        let binding = ParameterBinding::new(&parameters, &arguments);
        let values = BTreeMap::from([("bytes".to_string(), value.clone())]);
        let arrays = array_refs_for_parameters(&parameters, &values, state.memory());
        let names = BTreeSet::from(["bytes".to_string()]);
        let reassigned = CValue::typed_pointer(
            Pointer {
                block: "reassigned-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::Int32Pointer,
        );
        for (state, expected) in [
            (state.clone(), value),
            (
                state.clone().with_local("bytes", reassigned.clone()),
                reassigned,
            ),
        ] {
            let (all_values, all_arrays) = contract_environment_at_state(&values, &arrays, &state);
            assert_bytes(&all_values, &all_arrays, &expected, CType::Int32);
            let (named_values, named_arrays) =
                contract_environment_for_names(binding, &names, &state).unwrap();
            assert_bytes(&named_values, &named_arrays, &expected, CType::Int32);
        }
        // Without a shadowing parameter, the same name still denotes the global.
        let expected = CValue::typed_pointer(CMemory::global_pointer("bytes"), CType::UInt8Pointer);
        let (values, arrays) =
            contract_environment_at_state(&BTreeMap::new(), &BTreeMap::new(), &state);
        assert_bytes(&values, &arrays, &expected, CType::UInt8);
        let (values, arrays) =
            contract_environment_for_names(ParameterBinding::default(), &names, &state).unwrap();
        assert_bytes(&values, &arrays, &expected, CType::UInt8);
    }

    mod scaling_tests {
        include!("../../scaling_tests/surface/lowering/contract_environment.rs");
    }
}
