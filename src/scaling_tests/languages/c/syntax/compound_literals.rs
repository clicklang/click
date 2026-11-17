// Scaling tests for block-owned compound-literal storage in the C frontend.
use super::*;

#[test]
fn compound_literal_block_cleanup_uses_only_its_new_objects() {
    for count in [16usize, 64, 256] {
        let mut samples = Vec::new();
        for unrelated in [0, 64, 1024] {
            let mut parser = Parser::new("", CAbi::SUPPORTED).unwrap();
            parser.push_scope();
            for index in 0..unrelated {
                parser
                    .variable_types
                    .insert(format!("other_{index}").into(), InterfaceType::Int32);
            }
            let layout = RecordLayout::from_explicit_fields(
                vec![("value".into(), InterfaceType::Int32, 0, 4)],
                4,
                4,
            )
            .unwrap();
            for index in 0..count {
                parser
                    .compound_literal_declarations
                    .last_mut()
                    .unwrap()
                    .push(CStatement::DeclareStructValue {
                        name: BindingName::from(format!("literal_{index}")).into(),
                        layout: layout.clone(),
                        site: CSite::NONE,
                    });
            }
            let (body, work) = crate::instrumentation::measure_deterministic_work(|| {
                parser.finish_compound_literal_block(CStatement::Return(
                    CExpression::Int32Literal(0),
                    CSite::NONE,
                ))
            });
            assert_eq!(own_declarations(&body), count);
            let CStatement::Seq(_, cleanup) = body else {
                panic!("block cleanup")
            };
            let CStatement::EndAggregateLifetimes { names, steps, .. } = cleanup.as_ref() else {
                panic!("explicit lifetime end")
            };
            assert_eq!(names.len(), count);
            assert!(steps.is_empty());
            assert!(
                work >= count && work <= 8 * count + 4,
                "{count} literals, {unrelated} other locals: {work} work"
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|sample| sample[0] == sample[1]),
            "unrelated locals must not affect scope cleanup work"
        );
    }
}

#[test]
fn compound_literal_repeatable_value_uses_only_its_binding() {
    let mut samples = Vec::new();
    for unrelated in [0, 64, 1024] {
        let mut parser = Parser::new("", CAbi::SUPPORTED).unwrap();
        parser.binding_function = Some(LocalFunctionId::new(None, "f".into()));
        parser.push_scope();
        let name = parser.new_automatic_binding(Some("value".into()));
        parser
            .variable_types
            .insert(name.clone(), InterfaceType::Int32);
        for index in 0..unrelated {
            parser
                .variable_types
                .insert(format!("other_{index}").into(), InterfaceType::Int32);
        }
        let value = CExpression::Variable(name);
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            parser.repeatable_compound_literal_value(&value)
        });
        assert!(accepted);
        assert_eq!(work, 1);
        assert!(!parser.repeatable_compound_literal_value(&CExpression::Variable("global".into())));
        samples.push(work);
    }
    assert!(samples.windows(2).all(|sample| sample[0] == sample[1]));
}
