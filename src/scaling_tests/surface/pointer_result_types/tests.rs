use super::*;

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
        let ContractExpression::AlgebraicConstructor { arguments, .. } =
            &mut file.click_function_definitions[1].body
        else {
            panic!("constructor")
        };
        let mut argument = arguments.pop().unwrap();
        for _ in 0..depth {
            argument = ContractExpression::Call {
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
