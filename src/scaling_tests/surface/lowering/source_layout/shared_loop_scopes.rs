#[test]
fn continue_exit_metadata_skips_empty_enclosing_scopes() {
    for size in [4, 16, 64, 128] {
        let mut body = String::new();
        for _ in 0..size {
            body.push_str("if (1) { switch (0) { default: break; } ");
        }
        body.extend(std::iter::repeat_n('}', size));
        let source =
            format!("void scope_growth() {{ for (int32 i = 0; i < 1; i++) {{ {body} }} }}");
        let function = syntax::parse_function(&source).unwrap();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            SourceExecutionLayout::for_function(&function).unwrap()
        });
        assert!(work <= 80 * size + 300, "{size} scopes: {work}");
    }
}

#[test]
fn continue_exit_metadata_grows_with_the_locals_it_retires() {
    for size in [4, 16, 64, 128] {
        let declarations = (0..size)
            .map(|i| format!("int32 local_{i} = 0;"))
            .collect::<String>();
        let source = format!(
            "void locals_growth() {{ for (int32 i = 0; i < 1; i++) {{ {declarations} switch (i) {{ default: continue; }} }} }}"
        );
        let function = syntax::parse_function(&source).unwrap();
        let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
            SourceExecutionLayout::for_function(&function).unwrap()
        });
        assert!(
            layout
                .data
                .automatic_continue_exits
                .values()
                .any(|names| names.len() == size),
            "the switch continue retires all {size} body locals"
        );
        assert!(work <= 80 * size + 300, "{size} locals: {work}");
    }
}
