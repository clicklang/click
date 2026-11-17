use super::*;

fn parse_binding_expression(text: &str, source: &str) -> Result<ContractExpression, ClickError> {
    let function = syntax::parse_functions_for_source(source, "bindings.c")
        .unwrap()
        .remove(0);
    let mut layouts = ProgramLayouts::default();
    layouts.register_local_bindings(&function);
    let mut parser = Parser::new(text).unwrap();
    parser.local_bindings = layouts.local_bindings;
    parser.struct_layouts = function
        .structs()
        .iter()
        .map(|(name, layout)| (name.clone(), layout.clone()))
        .collect();
    parser.parse_contract_expression()
}

#[test]
fn source_declaration_selectors_resolve_the_same_typed_reference() {
    let source = "int f(int x) { int y = x; if (x) { int y = 7; } return y; }";
    let canonical = parse_binding_expression("f.local(0)", source).unwrap();
    assert_eq!(
        canonical,
        parse_binding_expression("f.statement(0).local(y)", source).unwrap()
    );
    assert_eq!(
        canonical,
        parse_binding_expression("\"bindings.c\"::f.local(0)", source).unwrap()
    );
    assert_ne!(
        canonical,
        parse_binding_expression("f.local(1)", source).unwrap()
    );
    let ContractExpression::ProgramExpression(ProgramExpression::Variable(
        crate::kernel::BindingName::Local(id),
    )) = canonical
    else {
        panic!("typed local")
    };
    assert_eq!(id.spelling(), Some("y"));
    assert_eq!(id.program_type(), Some(ProgramType::Int32));
    assert!(parse_binding_expression("f.local(99)", source).is_err());
    assert!(parse_binding_expression("f.statement(0).local(x)", source).is_err());
    assert!(parse_binding_expression("f.parameter(99)", source).is_err());
}

#[test]
fn declaration_references_retain_nominal_fields_and_array_shapes() {
    let source = "struct pair { int padding; int value; }; int f(void) { int a[2][3]; struct pair p; return 0; }";
    let field = parse_binding_expression("f.local(1).value", source).unwrap();
    assert!(matches!(
        field,
        ContractExpression::Field {
            offset_bytes: 4,
            ..
        }
    ));
    let array = parse_binding_expression("f.local(0)[1][2]", source).unwrap();
    assert!(
        matches!(array, ContractExpression::ArrayIndex { dimensions, .. } if dimensions == vec![2, 3])
    );
}

#[test]
fn exact_automatic_storage_instances_have_a_surface_spelling() {
    let source = "int f(int x) { return x; }";
    for (spelling, instance) in [
        ("implicit", crate::kernel::LocalStorageInstance::Implicit),
        (
            "parameter",
            crate::kernel::LocalStorageInstance::ValueParameter,
        ),
        (
            "lifetime, 7",
            crate::kernel::LocalStorageInstance::Lifetime(7),
        ),
        ("frame, 3", crate::kernel::LocalStorageInstance::Frame(3)),
    ] {
        let text = format!("f.parameter(0).storage({spelling})");
        let expression = parse_binding_expression(&text, source).unwrap();
        let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer,
        ))) = &expression
        else {
            panic!("storage pointer")
        };
        assert!(
            matches!(&pointer.pointer().block, crate::kernel::PointerBlock::AutomaticLocal { instance: actual, .. } if actual == &instance)
        );
        let rendered = crate::surface::diagnostics::describe_contract_expression(&expression);
        let reparsed = parse_binding_expression(&rendered, source).unwrap();
        let lowered = contract_expression_as_program_expression(&reparsed).unwrap();
        let (restored, _) = crate::kernel::program_evaluate_speprogram_expression_at_state(
            &ExecutionState::new(),
            &SpecExpression::ProgramExpression(lowered),
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(
            restored,
            ProgramValue::Pointer(pointer.clone()),
            "{rendered}"
        );
    }
}

#[test]
fn parameter_declaration_references_keep_pointer_field_syntax() {
    let expression = parse_binding_expression(
        "f.parameter(0)->value",
        "struct pair { int padding; int value; }; int f(struct pair *p) { return p->value; }",
    )
    .unwrap();
    assert!(matches!(
        expression,
        ContractExpression::Field {
            offset_bytes: 4,
            ..
        }
    ));
}

#[test]
fn function_statics_keep_types_and_exact_storage_spelling() {
    let source = "struct pair { int padding; int value; int storage; }; int f(void) { static int a[2][3]; static struct pair p; return 0; }";
    let array = parse_binding_expression("f.static(0)[1][2]", source).unwrap();
    assert!(
        matches!(array, ContractExpression::ArrayIndex { dimensions, .. } if dimensions == vec![2,3])
    );
    let field = parse_binding_expression("f.static(1).value", source).unwrap();
    assert!(matches!(
        field,
        ContractExpression::Field {
            offset_bytes: 4,
            ..
        }
    ));
    let field = parse_binding_expression("f.static(1).storage", source).unwrap();
    assert!(matches!(
        field,
        ContractExpression::Field {
            offset_bytes: 8,
            ..
        }
    ));
    let expression = parse_binding_expression("f.static(0).storage()", source).unwrap();
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
        pointer,
    ))) = expression
    else {
        panic!("static address");
    };
    assert!(matches!(
        pointer.pointer().block,
        crate::kernel::PointerBlock::StaticObject { .. }
    ));
    assert_eq!(
        crate::surface::diagnostics::describe_pointer(
            pointer.pointer(),
            crate::surface::ParameterBinding::default()
        ),
        "\"bindings.c\"::f.static(0).storage()"
    );
    assert!(parse_binding_expression("f.static(2)", source).is_err());
    assert!(parse_binding_expression("f.static(0).storage(frame, 1)", source).is_err());
}

fn parse_temporary_expression(text: &str) -> Result<ContractExpression, ClickError> {
    let mut function = syntax::parse_functions_for_source(
        "struct pair { int value; }; int f(void) { int x = 0; return x; }",
        "bindings.c",
    )
    .unwrap()
    .remove(0);
    let owner = crate::kernel::LocalFunctionId::new(Some("bindings.c".into()), "f".into());
    let scalar = crate::kernel::LocalBindingId::temporary(owner.clone(), 0);
    scalar.initialize_program_type(ProgramType::Int64);
    let object = crate::kernel::LocalBindingId::temporary(owner.clone(), 1);
    object.initialize_program_type(ProgramType::Int32Pointer);
    object.initialize_struct_name("pair");
    let payload = crate::kernel::LocalBindingId::temporary(owner, 2);
    payload.initialize_program_type(ProgramType::Int32);
    function = function.with_prelowered_kernel_function(crate::kernel::program_function(
        ProgramType::Int32,
        "f",
        Vec::new(),
        crate::kernel::program_seq(
            crate::kernel::program_declare(scalar, ProgramType::Int64),
            crate::kernel::program_seq(
                crate::kernel::program_declare_aggregate(
                    object,
                    crate::kernel::AggregateLayout::new(4, 4, Vec::new()),
                ),
                crate::kernel::program_try_catch_int32(
                    crate::kernel::program_skip(),
                    payload,
                    crate::kernel::program_skip(),
                ),
            ),
        ),
    ));
    let mut layouts = ProgramLayouts::default();
    layouts.register_local_bindings(&function);
    let mut parser = Parser::new(text)?;
    parser.local_bindings = layouts.local_bindings;
    parser.struct_layouts = function
        .structs()
        .iter()
        .map(|(name, layout)| (name.clone(), layout.clone()))
        .collect();
    parser.parse_contract_expression()
}

#[test]
fn temporary_selectors_preserve_types_owners_and_aggregate_fields() {
    let expression = parse_temporary_expression("f.temporary(0)").unwrap();
    assert_eq!(
        expression,
        parse_temporary_expression("\"bindings.c\"::f.temporary(0)").unwrap()
    );
    let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) = expression
    else {
        panic!("typed temporary");
    };
    assert_eq!(name.program_type(), Some(ProgramType::Int64));
    assert_eq!(name.source_spelling(), None);
    assert_ne!(
        parse_temporary_expression("f.local(0)").unwrap(),
        parse_temporary_expression("f.temporary(0)").unwrap()
    );
    assert!(matches!(
        parse_temporary_expression("f.temporary(1).value").unwrap(),
        ContractExpression::Field {
            offset_bytes: 0,
            ..
        }
    ));
    assert!(parse_temporary_expression("f.temporary(2)").is_ok());
    assert!(parse_temporary_expression("f.temporary(3)").is_err());
}

#[test]
fn temporary_storage_instances_round_trip_without_string_decoding() {
    for instance in ["implicit", "lifetime, 7", "frame, 11"] {
        let text = format!("f.temporary(1).storage({instance})");
        let expression = parse_temporary_expression(&text).unwrap();
        let raised = crate::surface::diagnostics::describe_contract_expression(&expression);
        let reparsed = parse_temporary_expression(&raised).unwrap();
        let lowered = contract_expression_as_program_expression(&reparsed).unwrap();
        let (restored, _) = crate::kernel::program_evaluate_speprogram_expression_at_state(
            &ExecutionState::new(),
            &SpecExpression::ProgramExpression(lowered),
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        let ContractExpression::ProgramExpression(ProgramExpression::Value(expected)) = expression
        else {
            panic!("storage pointer");
        };
        assert_eq!(restored, expected, "{raised}");
    }
}

#[test]
fn contract_result_slot_has_an_exact_surface_spelling() {
    let expression = parse_binding_expression("result.storage()", "int f(void) { return 0; }")
        .expect("typed result slot parses without a C declaration");
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
        pointer,
    ))) = expression
    else {
        panic!("a typed result slot pointer")
    };
    assert_eq!(
        pointer.pointer().block,
        crate::kernel::PointerBlock::ContractResult
    );
    assert_eq!(pointer.pointer().block.to_string(), "result.storage()");
    let text = crate::surface::diagnostics::describe_pointer(
        pointer.pointer(),
        crate::surface::ParameterBinding::default(),
    );
    assert_eq!(text, "result.storage()");
    assert_eq!(
        parse_binding_expression(&text, "int f(void) { return 0; }").unwrap(),
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer
        )))
    );
}

#[test]
fn contract_exception_slot_has_an_exact_surface_spelling() {
    let expression = parse_binding_expression("exception.storage()", "int f(void) { return 0; }")
        .expect("typed exception slot parses without a C declaration");
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
        pointer,
    ))) = expression
    else {
        panic!("a typed exception slot pointer")
    };
    assert_eq!(
        pointer.pointer().block,
        crate::kernel::PointerBlock::ContractException
    );
    assert_eq!(pointer.pointer().block.to_string(), "exception.storage()");
    let text = crate::surface::diagnostics::describe_pointer(
        pointer.pointer(),
        crate::surface::ParameterBinding::default(),
    );
    assert_eq!(text, "exception.storage()");
    assert_eq!(
        parse_binding_expression(&text, "int f(void) { return 0; }").unwrap(),
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer
        )))
    );
}

#[test]
fn exceptional_storage_rejects_frame_and_lifetime_arguments() {
    for spelling in [
        "exception.storage(frame, 1)",
        "exception.storage(lifetime, 1)",
        "exception.storage(1)",
    ] {
        assert!(parse_binding_expression(spelling, "int f(void) { return 0; }").is_err());
    }
}

#[test]
fn aggregate_return_storage_round_trips_the_full_frame_identity() {
    let source = "int f(void) { return 0; }";
    for frame in [0, 1, u32::MAX as u64 + 1, u64::MAX] {
        let text = format!("result.storage(frame, {frame})");
        let expression = parse_binding_expression(&text, source).unwrap();
        let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer,
        ))) = &expression
        else {
            panic!("typed return storage")
        };
        assert_eq!(
            pointer.pointer().block,
            crate::kernel::PointerBlock::AggregateReturn { frame }
        );
        assert_ne!(
            pointer.pointer().block,
            crate::kernel::PointerBlock::ContractResult
        );
        assert_eq!(pointer.pointer().block.to_string(), text);
        let raised = crate::surface::diagnostics::describe_pointer(
            pointer.pointer(),
            crate::surface::ParameterBinding::default(),
        );
        assert_eq!(raised, text);
        assert_eq!(
            parse_binding_expression(&raised, source).unwrap(),
            expression
        );
    }
    for invalid in [
        "result.storage(frame, -1)",
        "result.storage(frame, 18446744073709551616)",
        "result.storage(lifetime, 1)",
        "result.storage(frame)",
    ] {
        assert!(
            parse_binding_expression(invalid, source).is_err(),
            "{invalid}"
        );
    }
}
