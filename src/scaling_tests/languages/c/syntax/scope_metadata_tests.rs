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
