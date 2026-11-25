use super::*;

#[test]
fn integer_return_aliases_keep_linear_scoped_type_checking() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut source = String::from("function aliases() -> Integer { let v0: Integer = 0; ");
        for index in 1..size {
            source.push_str(&format!("let v{index}: Integer = v{} + 1; ", index - 1));
        }
        source.push_str(&format!("v{} }}", size - 1));
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| parser::parse(&source));
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
fn scalar_return_checking_scales_with_function_definitions() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut source = String::new();
        for index in 0..size {
            source.push_str(&format!(
                "function choose{index}(p: int32*, flag: int32) -> int32* {{ if flag == 0 {{ 0 }} else {{ p }} }} "
            ));
        }
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| parser::parse(&source));
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
fn recursive_return_interfaces_scale_with_definitions_and_calls() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut source = String::from(
            "spec enum Tree { Empty, Node(struct node*, Tree), } spec enum Ref { At(struct node*), } ",
        );
        for index in 0..size {
            source.push_str(&format!(
                "function get{index}(t: Tree) -> struct node* decreases t {{ match t {{ Tree::Empty => 0, Tree::Node(p, tail) => match tail {{ Tree::Empty => p, Tree::Node(q, rest) => get{index}(tail), }}, }} }} function wrap{index}(t: Tree) -> Ref {{ Ref::At(get{index}(t)) }} "
            ));
        }
        let file = parser::parse_file_items(&source).unwrap();
        let ((_, error), work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_result_types(
                file.click_function_definitions(),
                file.algebraic_type_definitions(),
            )
        });
        assert!(error.is_none(), "{error:?}");
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
fn shared_getter_analysis_scales_with_definitions_and_calls() {
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut source = String::from(
            "spec enum Ref { At(struct node*), } function get(m: Ref) -> struct node* { match m { Ref::At(p) => p, } } ",
        );
        for index in 0..size {
            source.push_str(&format!(
                "function f{index}(m: Ref) -> Ref {{ Ref::At(get(m)) }} "
            ));
        }
        let file = parser::parse_file_items(&source).unwrap();
        let ((_, error), work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_result_types(
                file.click_function_definitions(),
                file.algebraic_type_definitions(),
            )
        });
        assert!(error.is_none(), "{error:?}");
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
fn nested_getter_arguments_are_not_revisited_for_each_enclosing_call() {
    let mut samples = Vec::new();
    for depth in [8, 16, 32, 64] {
        // This isolates the analysis from the surface parser's nesting cap.
        let mut file = parser::parse_file_items("spec enum Ref { At(struct node*), } function id(p: struct node*) -> struct node* { p } function wrap(p: struct node*) -> Ref { Ref::At(p) }").unwrap();
        let SyntaxTerm::AlgebraicConstructor { arguments, .. } =
            file.click_function_definitions[1].body.as_mut().unwrap()
        else {
            panic!("constructor")
        };
        let mut argument = arguments.pop().unwrap();
        for _ in 0..depth {
            argument = SyntaxTerm::Call {
                name: "id".to_string(),
                arguments: vec![argument],
            };
        }
        arguments.push(argument);
        let ((_, error), work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_result_types(
                file.click_function_definitions(),
                file.algebraic_type_definitions(),
            )
        });
        assert!(error.is_none(), "{error:?}");
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 3, "{samples:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: enum guard checking across definition and lexical-scope sizes"]
fn algebraic_scalar_return_conditions_scale_with_definitions_and_scopes() {
    for grow_scopes in [false, true] {
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let mut source = String::from(
                "spec enum Color { Red, Black } spec enum Tree { Empty, Node(Color, Tree) } ",
            );
            if grow_scopes {
                source.push_str("function choose(t: Tree");
                for index in 0..size {
                    source.push_str(&format!(", unused{index}: Color"));
                }
                source.push_str(
                    ") -> int32 { match t { Tree::Empty => 0, Tree::Node(c, tail) => if ",
                );
                for _ in 0..size {
                    source.push_str("c == Color::Black and ");
                }
                source.push_str("0 == 0 { 1 } else { 0 }, } }");
            } else {
                for index in 0..size {
                    source.push_str(&format!("function choose{index}(t: Tree) -> int32 {{ match t {{ Tree::Empty => 0, Tree::Node(c, tail) => if c == Color::Black {{ 1 }} else {{ 0 }}, }} }} "));
                }
            }
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| parser::parse(&source));
            result.unwrap();
            assert!(work > 0);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "scopes={grow_scopes}: {samples:?}");
        }
    }
}
