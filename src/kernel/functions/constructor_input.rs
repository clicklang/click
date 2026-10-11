//! Matching scalar object requirements at symbolic entry and actual calls.
//! These requirements issue neither memory authority nor initialized bytes.
use super::*;

/// Source-obligation setup only. The same interface is validated at actual
/// calls by `bind`; an input spelling is never treated as a fresh allocation.
pub(crate) fn assume_scalar_object_inputs(
    mut state: CState,
    interface: &CFunctionContractInterface,
    arguments: &mut [CExpression],
) -> Result<CState, String> {
    for input in interface.aggregate_object_inputs() {
        let parameter = interface
            .parameters()
            .get(input.parameter_index)
            .ok_or("aggregate object input parameter is missing")?;
        if !parameter.c_type().is_pointer() {
            return Err("aggregate input must be a pointer".into());
        }
        let Some(CExpression::Value(CValue::Pointer(pointer))) =
            arguments.get_mut(input.parameter_index)
        else {
            return Err("aggregate object input is not an entry pointer value".into());
        };
        *pointer = CMemory::aggregate_input_pointer(
            pointer.pointer().clone(),
            &input.layout,
            pointer.c_type(),
        )
        .with_pointee_volatile(pointer.pointee_volatile())
        .with_pointee_constant(pointer.pointee_constant());
        state.set_memory(
            state
                .memory()
                .clone()
                .with_object_input_domain(pointer.pointer().clone(), &input.layout)?,
        );
    }
    for input in interface.scalar_object_inputs() {
        let parameter = interface
            .parameters()
            .get(input.parameter_index)
            .ok_or("scalar object input parameter is missing")?;
        if parameter.c_type().pointee_type() != Some(input.element_type) {
            return Err("scalar object input type does not match its parameter".into());
        }
        let Some(CExpression::Value(CValue::Pointer(pointer))) =
            arguments.get_mut(input.parameter_index)
        else {
            return Err("scalar object input is not an entry pointer value".into());
        };
        let address = pointer.pointer().clone();
        *pointer = pointer
            .clone()
            .with_designation(PointerDesignation::Object {
                root: address.clone(),
                path: Arc::from([]),
                base: address,
                element_type: input.element_type,
                stride: input.element_type.byte_width(),
                count: IntegerTerm::constant_i64(1).into(),
            });
        state.set_memory(
            state
                .memory()
                .clone()
                .with_scalar_input_domain(pointer.clone(), input.element_type)?,
        );
    }
    Ok(state)
}

/// This common hook is used by body execution, contract summaries and contract
/// certification. A raw address, even one equal to a scalar's address, cannot
/// establish the required complete pointer value.
pub(super) fn bind(
    caller: &CState,
    interface: &CFunctionContractInterface,
    callee: &CState,
) -> Option<()> {
    for input in interface.aggregate_object_inputs() {
        let parameter = interface.parameters().get(input.parameter_index)?;
        if !parameter.c_type().is_pointer() {
            return None;
        }
        let CValue::Pointer(pointer) = callee.locals.get(parameter.name())? else {
            return None;
        };
        if !caller
            .memory()
            .has_aggregate_object_domain(pointer, &input.layout)
        {
            return None;
        }
    }
    for input in interface.scalar_object_inputs() {
        let parameter = interface.parameters().get(input.parameter_index)?;
        if parameter.c_type().pointee_type() != Some(input.element_type) {
            return None;
        }
        let CValue::Pointer(pointer) = callee.locals.get(parameter.name())? else {
            return None;
        };
        if !caller
            .memory()
            .has_scalar_object_domain(pointer, input.element_type)
        {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw_function() -> CFunction {
        c_function(
            CType::Void,
            "scalar_input",
            vec![c_parameter("pointer", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
    }

    fn required_function() -> CFunction {
        raw_function().with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }])
    }

    #[test]
    fn scalar_object_requirement_is_semantic_interface_identity() {
        let ordinary = raw_function();
        let required = required_function();
        assert_ne!(ordinary, required);
        assert!(
            !ordinary
                .contract_interface()
                .exactly_matches(required.contract_interface())
        );
        assert!(
            !ordinary
                .contract_interface()
                .has_compatible_signature_and_composite_vocabulary(required.contract_interface())
        );
    }

    #[test]
    fn scalar_object_entry_and_shared_call_binding_require_the_same_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(940_100));
        let raw = CValue::typed_pointer(address.clone(), CType::Int32Pointer);
        let function = required_function();
        let mut arguments = vec![CExpression::Value(raw.clone())];
        assert!(
            bind_c_function_arguments(&CState::new(), &raw_function(), &[raw.clone()]).is_some()
        );
        assert!(bind_c_function_arguments(&CState::new(), &function, &[raw.clone()]).is_none());
        let state = assume_scalar_object_inputs(
            CState::new(),
            function.contract_interface(),
            &mut arguments,
        )
        .unwrap();
        assert!(!state.memory().has_block(&address.block));
        assert!(
            state.memory().cells.representation_len() == 0,
            "input validity must not seed values"
        );
        let CExpression::Value(actual) = &arguments[0] else {
            panic!()
        };
        assert!(bind_c_function_arguments(&state, &function, &[actual.clone()]).is_some());
        assert!(
            bind_c_contract_arguments(
                &state,
                function.contract_interface(),
                &[actual.clone()],
                None
            )
            .is_some()
        );
        assert!(bind_c_function_arguments(&state, &function, &[raw.clone()]).is_none());
        assert!(
            bind_c_contract_arguments(&state, function.contract_interface(), &[raw], None)
                .is_none()
        );
        let CValue::Pointer(actual) = actual else {
            panic!()
        };
        let different = actual.clone().with_designation(PointerDesignation::Object {
            root: address.clone(),
            path: vec![PointerDomainSelection::Member("different".into())].into(),
            base: address,
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        });
        assert!(
            bind_c_function_arguments(&state, &function, &[CValue::Pointer(different)]).is_none()
        );
    }
}

#[cfg(test)]
mod member_tests {
    use super::*;

    fn identity(name: &str) -> Option<Arc<CppRecordDeclarationIdentity>> {
        Some(Arc::new(CppRecordDeclarationIdentity::new(
            "member-input-test",
            name,
        )))
    }

    fn child(width: usize) -> CAggregateLayout {
        CAggregateLayout::new(
            (width as u32) * 4,
            4,
            (0..width)
                .map(|i| CAggregateField::new(format!("field{i}"), (i as u32) * 4, CType::Int32))
                .collect(),
        )
        .with_declaration_identity(identity("Child"))
    }

    fn parent(child: &CAggregateLayout) -> CAggregateLayout {
        CAggregateLayout::new(
            child.size_bytes() + 4,
            4,
            child
                .fields()
                .iter()
                .map(|field| {
                    CAggregateField::new(
                        format!("child.{}", field.name()),
                        field.offset_bytes(),
                        field.c_type(),
                    )
                })
                .chain(std::iter::once(CAggregateField::new(
                    "sibling",
                    child.size_bytes(),
                    CType::Int32,
                )))
                .collect(),
        )
        .with_records(vec![
            CAggregateRecord::new("child", 0, child.size_bytes(), 4, None)
                .with_declaration_identity(identity("Child")),
        ])
        .with_declaration_identity(identity("Parent"))
    }

    fn selected(
        memory: &CMemory,
        object: &CPointerValue,
        layout: &CAggregateLayout,
        path: &[&str],
        value_type: CType,
    ) -> CPointerValue {
        memory
            .checked_member_pointer(
                object,
                &CAggregateMemberSelection {
                    layout: Arc::new(layout.clone()),
                    path: path
                        .iter()
                        .map(|part| (*part).into())
                        .collect::<Vec<_>>()
                        .into(),
                    value_type,
                },
            )
            .expect("authenticated explicit member")
    }

    #[test]
    fn member_address_keeps_enclosing_root_through_entry_and_actual_call_binding() {
        let _session = crate::kernel::VerificationSession::enter();
        let child = child(2);
        let layout = parent(&child);
        let address = CMemory::frame_local_pointer(94, "parent");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let object = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap()
            .with_pointee_constant(true)
            .with_pointee_volatile(true);
        let member = selected(
            &memory,
            &object,
            &layout,
            &["child", "field0"],
            CType::Int32,
        );
        assert!(member.pointee_constant() && member.pointee_volatile());
        assert_eq!(member.pointer(), &address);
        let Some(PointerDesignation::Object { root, path, .. }) = member.designation() else {
            panic!()
        };
        assert_eq!(root, &address);
        assert_eq!(
            path.as_ref(),
            &[
                PointerDomainSelection::Member("child".into()),
                PointerDomainSelection::Member("field0".into())
            ]
        );
        let mut caller = CState::new();
        caller.set_memory(memory.clone());
        let expression = CExpression::MemberAddress {
            object: Box::new(CExpression::Value(CValue::Pointer(object.clone()))),
            selection: Arc::new(CAggregateMemberSelection {
                layout: Arc::new(layout.clone()),
                path: vec!["child".into(), "field0".into()].into(),
                value_type: CType::Int32,
            }),
        };
        let paths = crate::kernel::eval::evaluate_c_expression_paths(
            &caller,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].outcome,
            CExpressionOutcome::Value(CValue::Pointer(member.clone()))
        );
        assert!(paths[0].obligations.is_empty() && paths[0].facts.is_empty());
        let wrong_path = CAggregateMemberSelection {
            layout: Arc::new(layout.clone()),
            path: vec!["nonexistent".into()].into(),
            value_type: CType::Int32,
        };
        assert!(
            memory
                .checked_member_pointer(&object, &wrong_path)
                .is_none()
        );
        let function = c_function(
            CType::Void,
            "scalar_member",
            vec![
                c_parameter("pointer", CType::Int32Pointer)
                    .with_pointee_volatile(true)
                    .with_pointee_constant(true),
            ],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }]);
        let actual = CValue::Pointer(member.clone());
        let callee = bind_c_function_arguments(&caller, &function, &[actual.clone()]).unwrap();
        assert_eq!(callee.locals.get("pointer"), Some(&actual));
        assert!(
            bind_c_contract_arguments(&caller, function.contract_interface(), &[actual], None)
                .is_some()
        );
        // Equal addresses cannot rebase the member to a standalone scalar root.
        let rebased =
            CMemory::aggregate_input_pointer(address.clone(), &layout, CType::Int32Pointer)
                .with_designation(PointerDesignation::Object {
                    root: address.clone(),
                    path: Arc::from([]),
                    base: address.clone(),
                    element_type: CType::Int32,
                    stride: 4,
                    count: IntegerTerm::constant_i64(1).into(),
                });
        assert!(!memory.has_scalar_object_domain(&rebased, CType::Int32));
        assert!(!memory.has_scalar_object_domain(
            &member.clone().with_pointer(address.offset_by_bytes(4)),
            CType::Int32
        ));
        assert!(
            !memory.has_scalar_object_domain(
                &member
                    .clone()
                    .with_pointer(address.offset_by_bytes(child.size_bytes())),
                CType::Int32
            )
        );
        assert!(
            !memory
                .without_local_block(&address.block)
                .has_scalar_object_domain(&member, CType::Int32)
        );
        let raw = CPointerValue::new(address.clone(), object.c_type());
        assert!(
            memory
                .checked_member_pointer(
                    &raw,
                    &CAggregateMemberSelection {
                        layout: Arc::new(layout.clone()),
                        path: vec!["sibling".into()].into(),
                        value_type: CType::Int32
                    }
                )
                .is_none()
        );
        let record = selected(
            &memory,
            &object,
            &layout,
            &["child"],
            CType::UInt8Array(child.size_bytes()),
        );
        assert!(memory.has_aggregate_object_domain(&record, &child));
        // A successful memo must not authenticate a changed nominal definition.
        assert!(!memory.has_aggregate_object_domain(
            &record,
            &child.clone().with_declaration_identity(identity("Other"))
        ));
        let forged_shape = CAggregateLayout::new(
            child.size_bytes(),
            4,
            vec![
                CAggregateField::new("field0", 0, CType::UInt32),
                CAggregateField::new("field1", 4, CType::Int32),
            ],
        )
        .with_declaration_identity(identity("Child"));
        assert!(!memory.has_aggregate_object_domain(&record, &forged_shape));
        let wrong = memory.clone().with_declared_aggregate_block(
            address.block.clone(),
            &layout
                .clone()
                .with_declaration_identity(identity("OtherParent")),
        );
        assert!(!wrong.has_aggregate_object_domain(&object, &layout));
        assert!(
            wrong
                .checked_member_pointer(
                    &object,
                    &CAggregateMemberSelection {
                        layout: Arc::new(layout.clone()),
                        path: vec!["child".into(), "field0".into()].into(),
                        value_type: CType::Int32
                    }
                )
                .is_none()
        );
        assert!(!memory.has_initialized_bytes_under(&address, 4, &PureFactContext::new()));
    }

    #[test]
    fn aggregate_input_requirement_has_entry_actual_and_contract_parity_without_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(child(2));
        let function = c_function(
            CType::Void,
            "record_input",
            vec![c_parameter("pointer", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout: layout.clone(),
        }]);
        let address = Pointer::symbolic(Variable(940_300));
        let raw = CValue::typed_pointer(address.clone(), CType::Int32Pointer);
        assert!(bind_c_function_arguments(&CState::new(), &function, &[raw.clone()]).is_none());
        let mut arguments = vec![CExpression::Value(raw.clone())];
        let state = assume_scalar_object_inputs(
            CState::new(),
            function.contract_interface(),
            &mut arguments,
        )
        .unwrap();
        let CExpression::Value(actual) = &arguments[0] else {
            panic!()
        };
        assert!(bind_c_function_arguments(&state, &function, &[actual.clone()]).is_some());
        assert!(
            bind_c_contract_arguments(
                &state,
                function.contract_interface(),
                &[actual.clone()],
                None
            )
            .is_some()
        );
        assert!(!state.memory.has_block(&address.block));
        assert_eq!(state.memory.cells.representation_len(), 0);
        assert!(!state.memory.has_initialized_bytes_under(
            &address,
            layout.size_bytes(),
            &PureFactContext::new()
        ));
        assert!(state.resources().is_empty());
        let wrong =
            state
                .memory
                .clone()
                .with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
        let CValue::Pointer(actual) = actual else {
            panic!()
        };
        assert!(!wrong.has_aggregate_object_domain(actual, &layout));
    }

    #[test]
    fn member_address_selection_ignores_unrelated_fields_and_memoizes_large_selected_children() {
        let mut fixed = Vec::new();
        let mut nested = Vec::new();
        for width in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let child = child(width);
            let layout = parent(&child);
            let address = CMemory::frame_local_pointer(95, "parent");
            let memory =
                CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
            let object = memory
                .declared_aggregate_pointer(&address, &layout)
                .unwrap();
            let record = selected(
                &memory,
                &object,
                &layout,
                &["child"],
                CType::UInt8Array(child.size_bytes()),
            );
            assert!(memory.has_aggregate_object_domain(&record, &child)); // charge selected-shape admission once
            let fixed_selection = CAggregateMemberSelection {
                layout: Arc::new(layout.clone()),
                path: vec!["sibling".into()].into(),
                value_type: CType::Int32,
            };
            let child_selection = CAggregateMemberSelection {
                layout: Arc::new(child.clone()),
                path: vec!["field0".into()].into(),
                value_type: CType::Int32,
            };
            let fixed_expression = CExpression::MemberAddress {
                object: Box::new(CExpression::Value(CValue::Pointer(object.clone()))),
                selection: Arc::new(fixed_selection),
            };
            let child_expression = CExpression::MemberAddress {
                object: Box::new(CExpression::Value(CValue::Pointer(record.clone()))),
                selection: Arc::new(child_selection),
            };
            let mut state = CState::new();
            state.set_memory(memory.clone());
            let exercise = |expression: &CExpression| {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                std::hash::Hash::hash(expression, &mut hash);
                assert_eq!(
                    expression.cmp(&expression.clone()),
                    std::cmp::Ordering::Equal
                );
                let paths = crate::kernel::eval::evaluate_c_expression_paths(
                    &state,
                    expression,
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                )
                .unwrap();
                assert!(matches!(
                    paths.as_slice(),
                    [CExpressionPath {
                        outcome: CExpressionOutcome::Value(CValue::Pointer(_)),
                        ..
                    }]
                ));
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    exercise(&fixed_expression);
                }
            });
            fixed.push(work);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    exercise(&child_expression);
                }
            });
            nested.push(work);
        }
        assert!(
            fixed.iter().all(|work| *work <= fixed[0].max(1) * 2),
            "{fixed:?}"
        );
        assert!(
            nested.iter().all(|work| *work <= nested[0].max(1) * 2),
            "{nested:?}"
        );
    }
}
