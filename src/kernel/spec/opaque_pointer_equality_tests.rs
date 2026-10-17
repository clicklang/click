use super::*;

#[test]
fn opaque_extent_equality_retains_the_full_value_and_coverage() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(998_801));
    let extent = SubobjectExtent::opaque(Variable(SubobjectExtent::OPAQUE_VARIABLE_BASE + 81));
    let opaque =
        CPointerValue::new(base.clone(), CType::Int32Pointer).with_extent(Some(extent.clone()));
    let known = CPointerValue::new(base.clone(), CType::Int32Pointer)
        .with_extent(Some(SubobjectExtent::constant(base.clone(), 4)));
    let equality = c_value_comparison_proposition(
        &CValue::Pointer(opaque.clone()),
        CComparisonOperator::Equal,
        &CValue::Pointer(known.clone()),
    )
    .unwrap();
    let context = PureFactContext::new().assume_proposition(equality);
    assert!(!context.is_inconsistent());
    assert!(context.pointer_designations_match(&opaque, &known));
    assert!(context.opaque_extent_covers(&extent, &base, 4));
    assert!(!context.opaque_extent_covers(&extent, &base.offset_by_bytes(4), 4));
    let coverage = PureFactContext::new().assume_proposition(extent.coverage_fact(
        &CMemoryRange::new_with_element_width(base, 0u32.into(), 4u32.into(), 1),
    ));
    assert!(!coverage.pointer_designations_match(&opaque, &known));
}

#[test]
fn typed_ranges_keep_opaque_claims_and_root_widening_drops_them() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(998_802));
    let variable = Variable(SubobjectExtent::OPAQUE_VARIABLE_BASE + 82);
    let pointer = CPointerValue::new(base.clone(), CType::Int32Pointer)
        .with_extent(Some(SubobjectExtent::opaque(variable)))
        .with_member_extent(SubobjectExtent::constant(base.clone(), 4));
    let range = CMemoryRange::from_pointer_value(&pointer, 0u32.into(), 1u32.into(), 4);
    assert_eq!(range.designations(), [None, Some(variable)]);
    let copied = range.with_bounds(base.clone(), 0u32.into(), 1u32.into());
    assert_eq!(copied.designations(), range.designations());
    let root = pointer.with_root_extent();
    assert_eq!(root.designations(), [None, None]);
}

#[test]
fn implicit_void_pointer_coercions_preserve_complete_views_in_both_evaluators() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(998_803));
    let class = crate::kernel::effective_type::CAccessClass::Struct(
        crate::kernel::effective_type::CStructClass::opaque("pair"),
    );
    let opaque = CPointerValue::new(base.clone(), CType::Int32Pointer)
        .with_pointee_constant(true)
        .with_pointee_volatile(true)
        .with_object_class(Some(class.clone()));
    let member = opaque
        .clone()
        .with_member_extent(SubobjectExtent::constant(base, 4));
    for source in [opaque, member] {
        let expected = source.clone().with_type(CType::VoidPointer);
        let state = CState::new();
        let context = PureFactContext::new();
        let spec = SpecExpression::PointerCoercion(
            Box::new(SpecExpression::Value(CValue::Pointer(source.clone()))),
            CType::VoidPointer,
        );
        let paths = evaluate_spec_expression_paths_with_bindings(
            &state,
            &spec,
            &context,
            &BTreeMap::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one pointer value expected")
        };
        assert_eq!(path.value, CValue::Pointer(expected.clone()));
        let CValue::Pointer(actual) = &path.value else {
            unreachable!()
        };
        assert!(actual.pointee_constant());
        assert!(actual.pointee_volatile());
        assert!(actual.supports_object_class(&class));
        let native = CExpression::Cast {
            expression: Box::new(CExpression::Value(CValue::Pointer(source.clone()))),
            target_type: CType::VoidPointer,
            integer_mode: CIntegerCastMode::PointerCoercion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let paths = evaluate_c_expression_paths(
            &state,
            &native,
            &context,
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one pointer value expected")
        };
        assert_eq!(
            path.outcome,
            CExpressionOutcome::Value(CValue::Pointer(expected))
        );
        let explicit = SpecExpression::Cast(
            Box::new(SpecExpression::Value(CValue::Pointer(source))),
            CType::VoidPointer,
        );
        let paths = evaluate_spec_expression_paths_with_bindings(
            &state,
            &explicit,
            &context,
            &BTreeMap::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one pointer value expected")
        };
        let CValue::Pointer(root) = &path.value else {
            panic!("pointer expected")
        };
        assert!(root.extent_is_known());
        assert!(root.extent().is_none());
        assert_ne!(&path.value, &CValue::Pointer(actual.clone()));
    }
}

#[test]
fn implicit_void_pointer_coercion_rejects_function_pointers() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = CValue::typed_pointer(
        Pointer::symbolic(Variable(998_804)),
        CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    );
    let spec = SpecExpression::PointerCoercion(
        Box::new(SpecExpression::Value(source.clone())),
        CType::VoidPointer,
    );
    let state = CState::new();
    let context = PureFactContext::new();
    assert!(
        evaluate_spec_expression_paths_with_bindings(
            &state,
            &spec,
            &context,
            &BTreeMap::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap()
        .is_empty()
    );
    let native = CExpression::Cast {
        expression: Box::new(CExpression::Value(source)),
        target_type: CType::VoidPointer,
        integer_mode: CIntegerCastMode::PointerCoercion,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let paths = evaluate_c_expression_paths(
        &state,
        &native,
        &context,
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap();
    assert!(matches!(
        paths.as_slice(),
        [CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            ..
        }]
    ));
}

#[test]
fn native_pointer_word_round_trip_does_not_promote_declared_class_to_evidence() {
    let _session = crate::kernel::VerificationSession::enter();
    let class = crate::kernel::effective_type::CAccessClass::Struct(
        crate::kernel::effective_type::CStructClass::opaque("node"),
    );
    let source = CPointerValue::new(Pointer::symbolic(Variable(998_805)), CType::Int32Pointer)
        .with_declared_object_class(Some(class.clone()));
    for checked in [false, true] {
        let source = if checked {
            source.clone().with_object_class(Some(class.clone()))
        } else {
            source.clone()
        };
        let context = PureFactContext::new();
        let word = crate::kernel::eval::cast_c_value_to_type(
            CValue::Pointer(source),
            CType::UInt64,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let expression = CExpression::Cast {
            expression: Box::new(CExpression::Value(word)),
            target_type: CType::Int32Pointer,
            integer_mode: CIntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let paths = evaluate_c_expression_paths(
            &CState::new(),
            &expression,
            &context,
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one pointer expected")
        };
        let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &path.outcome else {
            panic!("pointer expected: {:?}", path.outcome)
        };
        assert_eq!(pointer.object_class(), Some(class.clone()));
        assert_eq!(pointer.supports_object_class(&class), checked);
    }
}
