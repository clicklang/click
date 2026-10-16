// Scaling tests of `src/languages/c/syntax.rs` (module `scope_metadata_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn explicit_embedded_layout_work_tracks_materialized_leaves() {
    for size in [8u32, 32, 128, 256] {
        let (layouts, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut layouts = BTreeMap::new();
            for index in 0..size {
                let mut fields = vec![("stamp".into(), C0Type::Int32, None, index * 4, 4)];
                if index != 0 {
                    fields.insert(
                        0,
                        (
                            "state".into(),
                            C0Type::Int32,
                            Some(format!("R{}", index - 1)),
                            0,
                            index * 4,
                        ),
                    );
                }
                let layout = C0StructLayout::from_explicit_fields_with_structs(
                    fields,
                    (index + 1) * 4,
                    4,
                    &layouts,
                )
                .unwrap();
                assert_eq!(layout.aggregate_fields.len(), index as usize + 1);
                assert_eq!(
                    layout.aggregate_fields.last().unwrap().offset_bytes,
                    index * 4
                );
                layouts.insert(format!("R{index}"), layout);
            }
            layouts
        });
        assert_eq!(layouts.len(), size as usize);
        assert_eq!(work, (size * (size - 1) / 2) as usize);
    }
}

/// Every parsed function keeps the declarations visible at its definition.
/// Those snapshots share one persistent map, so `n` functions after `n`
/// declarations hold one copy of them, not `n`. Interleaved declarations
/// still give each function exactly the ones declared before it.
#[test]
fn function_declaration_snapshots_share_the_translation_unit_maps() {
    for size in [8usize, 32, 128, 512] {
        let mut source = String::new();
        for index in 0..size {
            source.push_str(&format!(
                "struct S{index} {{ int32 a; }};\nint32 g{index};\n"
            ));
        }
        for index in 0..size {
            source.push_str(&format!("int32 f{index}(int32 x) {{ return x; }}\n"));
        }
        let functions = parse_functions(&source).unwrap();
        assert_eq!(functions.len(), size);
        let (structs, globals) = (functions[0].structs(), functions[0].globals());
        assert_eq!((structs.len(), globals.len()), (size, size));
        for function in &functions {
            assert!(function.structs().ptr_eq(structs), "size {size}");
            assert!(function.globals().ptr_eq(globals), "size {size}");
        }

        let mut interleaved = String::new();
        for index in 0..size {
            interleaved.push_str(&format!(
                "struct S{index} {{ int32 a; }};\nint32 f{index}(int32 x) {{ return x; }}\n"
            ));
        }
        let functions = parse_functions(&interleaved).unwrap();
        for (index, function) in functions.iter().enumerate() {
            assert_eq!(function.structs().len(), index + 1, "size {size}");
        }
    }
}
