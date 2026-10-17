use super::*;

fn analyze(source: &str) -> (BTreeMap<String, Origins>, Option<String>) {
    let file = parser::parse_file_items(source).unwrap();
    let (results, error) = pointer_result_types(
        file.click_function_definitions(),
        file.algebraic_type_definitions(),
    );
    (results, error.map(|(_, error)| error))
}

#[test]
fn constructor_and_forwarding_require_the_original_class() {
    let prefix =
        "spec enum Ref { At(struct node*), } function wrap(p: struct node*) -> Ref { Ref::At(p) }";
    assert!(analyze(prefix).1.is_none());
    for body in [
        "function wrong(p: struct other*) -> Ref { Ref::At(p) }",
        "function wrong(p: struct other*) -> Ref { wrap(p) }",
    ] {
        let error = analyze(&format!("{prefix} {body}")).1.unwrap();
        assert!(
            error.contains("requires original object class `struct node`"),
            "{error}"
        );
    }
}

#[test]
fn field_and_argument_origins_are_distinct_from_the_return_declaration() {
    let (results, error) = analyze(
        "spec enum Ref { At(struct node*), } function get(m: Ref) -> struct node* { match m { Ref::At(p) => p, } } function id(p: struct other*) -> struct node* { p }",
    );
    assert!(error.is_none(), "{error:?}");
    let field = results["get"].as_ref().unwrap();
    assert!(field.arguments.is_empty());
    assert_eq!(
        field.classes,
        BTreeSet::from([CAccessClass::Struct(CStructClass::opaque("node"))])
    );
    let parameter = results["id"].as_ref().unwrap();
    assert!(parameter.classes.is_empty());
    assert_eq!(parameter.arguments, BTreeSet::from([0]));
}

#[test]
fn match_bindings_shadow_parameter_origins_only_inside_the_arm() {
    let (_, error) = analyze(
        "spec enum Ref { At(struct node*), } function good(p: struct other*, m: Ref) -> Ref { match m { Ref::At(p) => Ref::At(p), } } function bad(p: struct other*, m: Ref) -> Ref { let x = match m { Ref::At(p) => Ref::At(p), }; Ref::At(p) }",
    );
    let error = error.unwrap();
    assert!(error.contains("function `bad`"), "{error}");
}

#[test]
fn generic_identity_preserves_the_actual_pointer_origin() {
    let (_, error) = analyze(
        "spec enum Ref { At(struct node*), } function id<T>(p: T) -> T { p } function wrap(p: struct node*) -> Ref { Ref::At(id(p)) }",
    );
    assert!(error.is_none(), "{error:?}");
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/pointer_result_types/tests.rs");
}
