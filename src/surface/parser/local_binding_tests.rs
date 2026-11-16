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
