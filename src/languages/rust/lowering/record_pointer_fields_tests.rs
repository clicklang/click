use crate::surface::C0VerificationSession;

#[test]
fn nested_box_fields_keep_their_pointer_type_in_old_reads() {
    let artifact = include_bytes!(
        "../../../../design/charon-trial/generic-stack/.click/generic_stack/stack.rs.ullbc"
    );
    let source = include_bytes!("../../../../design/charon-trial/generic-stack/stack.rs");
    let value: serde_json::Value = serde_json::from_slice(artifact).unwrap();
    let config = serde_json::from_value(value["crate_config"].clone()).unwrap();
    let sources = [("stack.rs".into(), source.to_vec())].into_iter().collect();
    let mut export = super::super::charon::decode_crate(
        artifact,
        "stack.rs",
        source,
        Some(&config),
        Some(&sources),
    )
    .unwrap();
    // Check the existing generic method alone; no instantiated caller or drop
    // contract is needed to observe the nested pointer field's layout.
    export
        .functions
        .retain(|function| function.name.ends_with("_A1_T_I4_size"));
    assert_eq!(export.functions.len(), 1);
    let (_, layouts) = super::lower(&export).unwrap();
    let stack = layouts
        .iter()
        .find(|(name, _)| name.ends_with("_I5_Stack_A1_T"))
        .expect("the generic stack layout")
        .1;
    let node_name = stack
        .field("head")
        .unwrap()
        .struct_name()
        .expect("head retains its pointee record");
    let next = layouts[node_name].field("next").unwrap();
    assert_eq!(next.offset_bytes(), 8);
    assert_eq!(next.struct_name(), Some(node_name));
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let source = r#"
        verifying "stack.rs";
        impl<T> generic_stack::Stack<T> {
            fn size(&self) -> usize {
                views self.head;
                views self.len;
                views self.head.next;
                requires self.head != 0;
                requires self.head.next != 0;
                ensures same_object(self.head.next, old(self.head.next));
            }
        }
    "#;
    C0VerificationSession::new_program_prepared(source, &prepared)
        .unwrap_or_else(|error| panic!("{error}"));
    let missing_field = source.replace("head.next", "head.missing");
    let error = C0VerificationSession::new_program_prepared(&missing_field, &prepared)
        .err()
        .expect("a named record has no arbitrary fields");
    assert!(
        error.to_string().contains("has no field `missing`"),
        "{error}"
    );
}
