// Scaling tests of `src/surface/lowering/annotations.rs` (module `local_pointer_type_index_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// Index work is one traversal, independent of how many typed locals the
// selected function declares. Distinct frontend bindings retain types.
#[test]
fn local_pointer_types_index_once_with_linear_work() {
    for count in [16, 64, 256] {
        let mut body = crate::kernel::c_skip();
        for index in 0..count {
            body = c_seq(
                body,
                crate::kernel::c_declare(
                    format!("local_{index}"),
                    if index % 2 == 0 {
                        CType::UInt8Pointer
                    } else {
                        CType::UInt64Pointer
                    },
                ),
            );
        }
        let mut types = BTreeMap::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            collect_local_pointer_element_types(&body, &mut types);
        });
        assert_eq!(work, 2 * count + 1);
        assert_eq!(types.len(), count);
        for index in 0..count {
            assert_eq!(
                types[&format!("local_{index}")],
                if index % 2 == 0 {
                    CType::UInt8
                } else {
                    CType::UInt64
                }
            );
        }
    }
}
