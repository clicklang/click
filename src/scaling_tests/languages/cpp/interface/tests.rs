use super::*;

#[test]
fn source_record_layouts_are_shared_and_lookup_is_indexed() {
    use crate::languages::interface::{ImportedFunction, RecordLayout};
    for size in [1, 16, 64, 256] {
        let leaf = RecordLayout::from_explicit_fields(
            vec![("value".into(), InterfaceType::Int32, 0, 4)],
            4,
            4,
        )
        .unwrap();
        let layouts = std::sync::Arc::new(
            (0..size)
                .map(|index| (format!("Record{index}"), leaf.clone()))
                .collect::<BTreeMap<_, _>>(),
        );
        let (functions, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..size)
                .map(|index| {
                    crate::instrumentation::record_deterministic_work(1);
                    let mut function = ImportedFunction::external(
                        InterfaceType::Void,
                        format!("f{index}"),
                        Vec::new(),
                    );
                    function.prepared_record_layouts = layouts.clone();
                    function
                })
                .collect::<Vec<_>>()
        });
        assert_eq!(work, size);
        for function in &functions {
            assert!(std::sync::Arc::ptr_eq(
                &function.prepared_record_layouts,
                &layouts
            ));
        }
        let (_, lookup) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(functions[0].record_layout("Record0").is_some());
            assert!(functions[0].record_layout("Missing").is_none());
        });
        assert_eq!(lookup, 2, "lookup in {size} declarations/functions");
    }
}

#[test]
fn qualified_callback_signatures_keep_const_with_linear_parameter_work() {
    for size in [1, 16, 256, 1024] {
        let pointer = CppType::Pointer {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: true,
                source_aliases: Vec::new(),
            }),
        };
        let callback = CppType::FunctionPointer {
            return_type: Box::new(pointer.clone()),
            parameters: vec![pointer; size],
            is_const: false,
        };
        let (signature, work) = crate::instrumentation::measure_deterministic_work(|| {
            function_pointer_signature(&callback).unwrap()
        });
        assert_eq!(signature.parameters.len(), size);
        assert!(signature.return_pointee_constant);
        assert!(
            signature
                .parameters
                .iter()
                .all(|parameter| parameter.pointee_constant)
        );
        assert_eq!(work, size);
    }
}
