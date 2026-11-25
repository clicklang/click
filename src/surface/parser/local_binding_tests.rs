use super::*;

fn parse_binding_expression(text: &str, source: &str) -> Result<SyntaxTerm, ClickError> {
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
    let SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
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
fn compound_literal_occurrences_are_distinct_from_local_declarations() {
    let source = r#"
        struct pair { int padding; int value; };
        int f(void) {
            int *array = (int[]){42};
            struct pair *pair = &(struct pair){0, 42};
            int after = array[0] + pair->value;
            return after;
        }
    "#;
    let array = parse_binding_expression("f.compound_literal(0)", source).unwrap();
    let field = parse_binding_expression("f.compound_literal(1).value", source).unwrap();
    assert!(matches!(
        field,
        SyntaxTerm::Field {
            offset_bytes: crate::kernel::LayoutOffset::Bytes(4),
            ..
        }
    ));
    assert_eq!(
        array,
        parse_binding_expression("\"bindings.c\"::f.compound_literal(0)", source).unwrap()
    );
    assert_eq!(
        parse_binding_expression("f.local(4)", source).unwrap(),
        parse_binding_expression("f.statement(2).local(after)", source).unwrap()
    );
    assert!(parse_binding_expression("f.local(1)", source).is_err());
    assert!(parse_binding_expression("f.compound_literal(2)", source).is_err());

    assert_automatic_storage_reference_round_trips(
        "f.compound_literal(1).storage(lifetime, 7)",
        source,
        crate::kernel::LocalStorageInstance::Lifetime(7),
    );
}

#[test]
fn declaration_references_retain_nominal_fields_and_array_shapes() {
    let source = "struct pair { int padding; int value; }; int f(void) { int a[2][3]; struct pair p; return 0; }";
    let field = parse_binding_expression("f.local(1).value", source).unwrap();
    assert!(matches!(
        field,
        SyntaxTerm::Field {
            offset_bytes: crate::kernel::LayoutOffset::Bytes(4),
            ..
        }
    ));
    let array = parse_binding_expression("f.local(0)[1][2]", source).unwrap();
    assert!(matches!(array, SyntaxTerm::ArrayIndex { dimensions, .. } if dimensions == vec![2, 3]));
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
        assert_automatic_storage_reference_round_trips(
            &format!("f.parameter(0).storage({spelling})"),
            source,
            instance,
        );
    }
}

fn assert_automatic_storage_reference_round_trips(
    text: &str,
    source: &str,
    instance: crate::kernel::LocalStorageInstance,
) {
    let expression = parse_binding_expression(text, source).unwrap();
    let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer))) =
        &expression
    else {
        panic!("storage pointer")
    };
    assert!(
        matches!(&pointer.address().base, crate::kernel::AddressBase::AutomaticLocal { instance: actual, .. } if actual == &instance)
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

#[test]
fn parameter_declaration_references_keep_pointer_field_syntax() {
    let expression = parse_binding_expression(
        "f.parameter(0)->value",
        "struct pair { int padding; int value; }; int f(struct pair *p) { return p->value; }",
    )
    .unwrap();
    assert!(matches!(
        expression,
        SyntaxTerm::Field {
            offset_bytes: crate::kernel::LayoutOffset::Bytes(4),
            ..
        }
    ));
}

#[test]
fn function_statics_keep_types_and_exact_storage_spelling() {
    let source = "struct pair { int padding; int value; int storage; }; int f(void) { static int a[2][3]; static struct pair p; return 0; }";
    let array = parse_binding_expression("f.static(0)[1][2]", source).unwrap();
    assert!(matches!(array, SyntaxTerm::ArrayIndex { dimensions, .. } if dimensions == vec![2,3]));
    let field = parse_binding_expression("f.static(1).value", source).unwrap();
    assert!(matches!(
        field,
        SyntaxTerm::Field {
            offset_bytes: crate::kernel::LayoutOffset::Bytes(4),
            ..
        }
    ));
    let field = parse_binding_expression("f.static(1).storage", source).unwrap();
    assert!(matches!(
        field,
        SyntaxTerm::Field {
            offset_bytes: crate::kernel::LayoutOffset::Bytes(8),
            ..
        }
    ));
    let expression = parse_binding_expression("f.static(0).storage()", source).unwrap();
    let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer))) =
        expression
    else {
        panic!("static address");
    };
    assert!(matches!(
        pointer.address().base,
        crate::kernel::AddressBase::StaticObject { .. }
    ));
    assert_eq!(
        crate::surface::diagnostics::describe_pointer(
            pointer.address(),
            crate::surface::ParameterBinding::default()
        ),
        "\"bindings.c\"::f.static(0).storage()"
    );
    assert!(parse_binding_expression("f.static(2)", source).is_err());
    assert!(parse_binding_expression("f.static(0).storage(frame, 1)", source).is_err());
}

#[test]
fn frontend_temporaries_have_no_declaration_selector() {
    let owner = crate::kernel::LocalFunctionId::new(Some("bindings.c".into()), "f".into());
    let temporary = crate::kernel::LocalBindingId::temporary(owner, 0);
    temporary.initialize_program_type(ProgramType::Int64);
    let mut bindings = SourceBindingIndex::default();
    bindings
        .owners
        .insert("f".into(), [Some("bindings.c".into())].into());
    bindings
        .declarations
        .insert(temporary, SourceBindingInfo::default());
    let bindings = std::sync::Arc::new(bindings);
    for selector in [
        "f.temporary(0)",
        "\"bindings.c\"::f.temporary(0)",
        "f.temporary(0).storage(lifetime, 7)",
    ] {
        let mut parser = Parser::new(selector).unwrap();
        parser.local_bindings = bindings.clone();
        assert!(
            parser.take_local_binding_reference().unwrap().is_none(),
            "{selector}"
        );
    }
}

#[test]
fn contract_result_slot_has_an_exact_surface_spelling() {
    let expression = parse_binding_expression("result.storage()", "int f(void) { return 0; }")
        .expect("typed result slot parses without a C declaration");
    let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer))) =
        expression
    else {
        panic!("a typed result slot pointer")
    };
    assert_eq!(
        pointer.address().base,
        crate::kernel::AddressBase::ContractResult
    );
    assert_eq!(pointer.address().base.to_string(), "result.storage()");
    let text = crate::surface::diagnostics::describe_pointer(
        pointer.address(),
        crate::surface::ParameterBinding::default(),
    );
    assert_eq!(text, "result.storage()");
    assert_eq!(
        parse_binding_expression(&text, "int f(void) { return 0; }").unwrap(),
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer)))
    );
}

#[test]
fn contract_exception_slot_has_an_exact_surface_spelling() {
    let expression = parse_binding_expression("exception.storage()", "int f(void) { return 0; }")
        .expect("typed exception slot parses without a C declaration");
    let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer))) =
        expression
    else {
        panic!("a typed exception slot pointer")
    };
    assert_eq!(
        pointer.address().base,
        crate::kernel::AddressBase::ContractException
    );
    assert_eq!(pointer.address().base.to_string(), "exception.storage()");
    let text = crate::surface::diagnostics::describe_pointer(
        pointer.address(),
        crate::surface::ParameterBinding::default(),
    );
    assert_eq!(text, "exception.storage()");
    assert_eq!(
        parse_binding_expression(&text, "int f(void) { return 0; }").unwrap(),
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer)))
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
        let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(pointer))) =
            &expression
        else {
            panic!("typed return storage")
        };
        assert_eq!(
            pointer.address().base,
            crate::kernel::AddressBase::AggregateReturn { frame }
        );
        assert_ne!(
            pointer.address().base,
            crate::kernel::AddressBase::ContractResult
        );
        assert_eq!(pointer.address().base.to_string(), text);
        let raised = crate::surface::diagnostics::describe_pointer(
            pointer.address(),
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
