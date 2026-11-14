use super::*;

#[test]
fn implicit_void_pointer_coercions_preserve_complete_views_in_both_evaluators() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(998_803));
    let class = crate::kernel::effective_type::CAccessClass::Struct(
        crate::kernel::effective_type::CStructClass::opaque("pair"),
    );
    let opaque = PointerValue::new(base.clone(), ProgramType::Int32Pointer)
        .with_pointee_constant(true)
        .with_pointee_volatile(true)
        .with_object_class(Some(class.clone()));
    let member = opaque
        .clone()
        .with_extent(Some(SubobjectExtent::constant(base, 4)));
    for source in [opaque, member] {
        let expected = source.clone().with_type(ProgramType::VoidPointer);
        let state = ExecutionState::new();
        let context = PureFactContext::new();
        let spec = SpecExpression::PointerCoercion(
            Box::new(SpecExpression::Value(ProgramValue::Pointer(source.clone()))),
            ProgramType::VoidPointer,
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
        assert_eq!(
            path.value.clone().into_native(),
            ProgramValue::Pointer(expected.clone())
        );
        let ProgramValue::Pointer(actual) = &path.value.clone().into_native() else {
            unreachable!()
        };
        assert!(actual.pointee_constant());
        assert!(actual.pointee_volatile());
        assert!(actual.supports_object_class(&class));
        let native = ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(ProgramValue::Pointer(
                source.clone(),
            ))),
            target_type: ProgramType::VoidPointer,
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
            CExpressionOutcome::Value(ProgramValue::Pointer(expected))
        );
        let explicit = SpecExpression::Cast(
            Box::new(SpecExpression::Value(ProgramValue::Pointer(source))),
            ProgramType::VoidPointer,
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
        let ProgramValue::Pointer(root) = &path.value.clone().into_native() else {
            panic!("pointer expected")
        };
        assert!(root.extent_is_known());
        assert!(root.extent().is_none());
        assert_ne!(
            &path.value.clone().into_native(),
            &ProgramValue::Pointer(actual.clone())
        );
    }
}

#[test]
fn implicit_void_pointer_coercion_rejects_function_pointers() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = ProgramValue::typed_pointer(
        Pointer::symbolic(Variable(998_804)),
        ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    );
    let spec = SpecExpression::PointerCoercion(
        Box::new(SpecExpression::Value(source.clone())),
        ProgramType::VoidPointer,
    );
    let state = ExecutionState::new();
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
    let native = ProgramExpression::Cast {
        expression: Box::new(ProgramExpression::Value(source)),
        target_type: ProgramType::VoidPointer,
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
    let source = PointerValue::new(
        Pointer::symbolic(Variable(998_805)),
        ProgramType::Int32Pointer,
    )
    .with_declared_object_class(Some(class.clone()));
    for checked in [false, true] {
        let source = if checked {
            source.clone().with_object_class(Some(class.clone()))
        } else {
            source.clone()
        };
        let context = PureFactContext::new();
        let word = crate::kernel::eval::cast_c_value_to_type(
            ProgramValue::Pointer(source),
            ProgramType::UInt64,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &context,
        )
        .unwrap();
        let expression = ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(word)),
            target_type: ProgramType::Int32Pointer,
            integer_mode: CIntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let paths = evaluate_c_expression_paths(
            &ExecutionState::new(),
            &expression,
            &context,
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        let [path] = paths.as_slice() else {
            panic!("one pointer expected")
        };
        let CExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &path.outcome else {
            panic!("pointer expected: {:?}", path.outcome)
        };
        assert_eq!(pointer.object_class(), Some(class.clone()));
        assert_eq!(pointer.supports_object_class(&class), checked);
    }
}
