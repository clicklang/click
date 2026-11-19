use super::*;

#[test]
fn bit_field_lookup_work_is_independent_of_other_bindings_and_words() {
    let mut measurements = Vec::new();
    for unrelated in [0, 64, 1024] {
        let prefix: String = (0..unrelated)
            .map(|index| format!("unsigned int prefix_{index} : 32; "))
            .collect();
        let source = format!("struct flags {{ {prefix} unsigned int ready : 29; }}; f.ready");
        let mut parser = Parser::new(&source, CAbi::SUPPORTED).unwrap();
        parser.parse_struct_declaration().unwrap();
        parser.push_scope();
        let record = parser.bit_field_records["flags"].clone();
        let f = parser.declare_name("f").unwrap();
        let object = LocalBitFields {
            record,
            storage: f.clone(),
            pointer: None,
            read_only: false,
        };
        for n in 0..unrelated {
            let binding = parser.declare_name(&format!("other_{n}")).unwrap();
            parser.local_bit_fields.insert(binding, object.clone());
        }
        parser.local_bit_fields.insert(f, object);
        let (parsed, work) =
            crate::instrumentation::measure_deterministic_work(|| parser.parse_primary());
        assert!(parsed.is_ok());
        assert!(work >= 4);
        measurements.push(work);
    }
    assert!(
        measurements.windows(2).all(|sample| sample[0] == sample[1]),
        "{measurements:?}"
    );
}

#[test]
fn bit_field_pointer_copy_uses_only_the_selected_bindings() {
    let mut measurements = Vec::new();
    for unrelated in [0, 64, 1024] {
        let mut parser = Parser::new(
            "struct flags { unsigned int ready : 1; }; struct flags f = {1}; struct flags g = {0}; struct flags *p = &f; *p = g;",
            CAbi::SUPPORTED,
        ).unwrap();
        parser.parse_struct_declaration().unwrap();
        parser.binding_function = Some(LocalFunctionId::new(None, "copy".into()));
        parser.push_scope();
        for _ in 0..3 {
            parser.parse_local_declaration().unwrap();
        }
        let object = parser.local_bit_fields[&parser.resolve_name("f")].clone();
        for n in 0..unrelated {
            let binding = parser.declare_name(&format!("other_{n}")).unwrap();
            parser.local_bit_fields.insert(binding, object.clone());
        }
        let (parsed, work) = crate::instrumentation::measure_deterministic_work(|| {
            parser.parse_local_bit_field_store()
        });
        assert!(parsed.unwrap().is_some());
        assert!(work > 0);
        measurements.push(work);
    }
    assert!(
        measurements.windows(2).all(|sample| sample[0] == sample[1]),
        "{measurements:?}"
    );
}
