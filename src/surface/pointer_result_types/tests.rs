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
fn typed_returns_check_the_body_and_publish_the_declared_class() {
    let (results, error) = analyze(
        "spec enum Ref { At(struct node*), } function get(m: Ref) -> struct node* { match m { Ref::At(p) => p, } } function id(p: struct node*) -> struct node* { p }",
    );
    assert!(error.is_none(), "{error:?}");
    let field = results["get"].as_ref().unwrap();
    assert!(field.arguments.is_empty());
    assert_eq!(
        field.classes,
        BTreeSet::from([CAccessClass::Struct(CStructClass::opaque("node"))])
    );
    let parameter = results["id"].as_ref().unwrap();
    assert_eq!(parameter.classes, field.classes);
    assert!(parameter.arguments.is_empty());
}

#[test]
fn unused_functions_cannot_lie_about_their_return_class() {
    for body in [
        "function wrong(p: struct other*) -> struct node* { p }",
        "spec enum Ref { At(struct other*), } function wrong(m: Ref) -> struct node* { match m { Ref::At(p) => p, } }",
        "function wrong(p: struct other*, flag: int32) -> struct node* { if flag == 0 { 0 } else { p } }",
    ] {
        let error = analyze(body).1.unwrap();
        assert!(
            error.contains("return value requires original object class `struct node`"),
            "{error}"
        );
    }
}

#[test]
fn recursive_returns_use_the_checked_function_interface() {
    let (_, error) = analyze(
        "spec enum Tree { Empty, Node(struct node*, Tree), } function parent(t: Tree) -> struct node* decreases t { match t { Tree::Empty => 0, Tree::Node(p, left) => match left { Tree::Empty => p, Tree::Node(q, rest) => parent(left), }, } } spec enum Ref { At(struct node*), } function wrap(t: Tree) -> Ref { Ref::At(parent(t)) }",
    );
    assert!(error.is_none(), "{error:?}");
}

#[test]
fn recursive_returns_still_check_every_base_case() {
    let (_, error) = analyze(
        "spec enum Tree { Empty, Node(struct other*, Tree), } function parent(t: Tree) -> struct node* decreases t { match t { Tree::Empty => 0, Tree::Node(p, left) => match left { Tree::Empty => p, Tree::Node(q, rest) => parent(left), }, } }",
    );
    let error = error.unwrap();
    assert!(error.contains("function `parent` return value"), "{error}");
}

#[test]
fn forwarding_cannot_hide_an_invalid_return_definition() {
    let (_, error) = analyze(
        "function forward(p: struct other*) -> struct node* { wrong(p) } function wrong(p: struct other*) -> struct node* { p }",
    );
    let error = error.unwrap();
    assert!(error.contains("function `wrong` return value"), "{error}");
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

#[test]
fn enum_match_fields_keep_their_types_in_scalar_return_conditions() {
    let prefix = "spec enum Color { Red, Black } spec enum Tree { Empty, Node(Color, Tree) } ";
    for condition in [
        "c == Color::Black",
        "Color::Black == c",
        "c != Color::Red",
        "not (c == Color::Red)",
        "c == Color::Black and 0 == 0",
        "0 == 1 or c == Color::Black",
    ] {
        for (result, yes, no) in [
            ("int32", "1", "0"),
            ("Bool", "true", "false"),
            ("int32*", "p", "0"),
        ] {
            let source = format!(
                "{prefix} function choose(t: Tree, p: int32*) -> {result} {{ match t {{ Tree::Empty => {no}, Tree::Node(c, tail) => if {condition} {{ {yes} }} else {{ {no} }}, }} }}"
            );
            parser::parse(&source).unwrap_or_else(|error| panic!("{condition}: {error:?}"));
        }
    }
}

#[test]
fn scalar_return_conditions_retain_comparison_type_rejections() {
    let prefix = "spec enum Color { Red, Black } spec enum Other { Red } spec enum Tree { Empty, Node(Color, Tree) } ";
    for condition in [
        "c == Other::Red",
        "c == 0",
        "c < Color::Black",
        "c == Color::Black and true == 1",
        "c == Color::Black and [1] == [true]",
        "true == 1",
        "[1] == [true]",
    ] {
        let source = format!(
            "{prefix} function wrong(t: Tree) -> int32 {{ match t {{ Tree::Empty => 0, Tree::Node(c, tail) => if {condition} {{ 1 }} else {{ 0 }}, }} }}"
        );
        assert!(parser::parse(&source).is_err(), "accepted {condition}");
    }
    for condition in ["[1] == [1]", "([1] ++ [2]) == [1, 2]"] {
        let source =
            format!("function sequence_guard() -> int32 {{ if {condition} {{ 1 }} else {{ 0 }} }}");
        parser::parse(&source).unwrap_or_else(|error| panic!("{condition}: {error:?}"));
    }
}
