use super::*;

#[test]
fn bit_field_lookup_work_is_independent_of_other_bindings() {
    let mut measurements = Vec::new();
    for unrelated in [0, 64, 1024] {
        let mut parser = Parser::new(
            "struct flags { unsigned int ready : 1; }; f.ready",
            CAbi::SUPPORTED,
        )
        .unwrap();
        parser.parse_struct_declaration().unwrap();
        parser.push_scope();
        let record = parser.bit_field_records["flags"].clone();
        let f = parser.declare_name("f").unwrap();
        let object = LocalBitFields {
            record,
            word: BindingName::from("private"),
            partial: None,
        };
        for n in 0..unrelated {
            let binding = parser.declare_name(&format!("other_{n}")).unwrap();
            parser.local_bit_fields.insert(binding, object.clone());
        }
        parser.local_bit_fields.insert(f, object);
        let (parsed, work) =
            crate::instrumentation::measure_deterministic_work(|| parser.parse_primary());
        assert!(parsed.is_ok());
        assert!(work > 0);
        measurements.push(work);
    }
    assert!(
        measurements.windows(2).all(|sample| sample[0] == sample[1]),
        "{measurements:?}"
    );
}
