use super::*;

#[test]
fn row_pointer_access_uses_one_binding_and_a_fixed_width_calculation() {
    for columns in [3, 1024, 1_000_000] {
        let work = [0, 64, 1024].map(|unrelated| {
            let mut parser = Parser::new("[1][0]", CAbi::SUPPORTED).unwrap();
            let row: BindingName = "row".into();
            for index in 0..unrelated {
                let name: BindingName = format!("other_row_{index}").into();
                parser.local_row_pointers.insert(
                    name,
                    LocalRowPointer {
                        element_type: InterfaceType::Int32,
                        columns: 2,
                    },
                );
            }
            parser.variable_types.insert(row.clone(), InterfaceType::Int32Pointer);
            parser.local_row_pointers.insert(
                row.clone(),
                LocalRowPointer { element_type: InterfaceType::Int32, columns },
            );
            let (expression, work) = crate::instrumentation::measure_deterministic_work(|| {
                parser.parse_postfix_tail(CExpression::Variable(row), true)
            });
            let CExpression::Index(base, _, _) = expression.unwrap() else {
                panic!("row element access")
            };
            assert!(matches!(base.as_ref(), CExpression::Subobject { width, .. } if *width == 4 * columns));
            work
        });
        assert_eq!(work, [1; 3]);
    }
}
