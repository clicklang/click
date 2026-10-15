// Scaling tests of `src/languages/cpp/validity.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn metadata_work_scales_with_nodes_and_aliases_without_outer_environments() {
    let sources = BTreeSet::from(["fixture.cpp".into(), "types.hpp".into()]);
    for size in [4, 32, 256, 1024] {
        let statement = json!({"kind":"return_call","callee":reference(),"arguments":call_arguments(),"value_type":ty(),"cleanups":[cleanup()],"span":span()});
        let function = fixture(Value::Array(vec![statement; size]));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            check_function(&function, "fixture.cpp", &sources)
        });
        result.unwrap();
        assert_eq!(work, 4 + 16 * size);
    }
    // Type wrappers and aliases are structural; widths and pointee support
    // are left to the semantic validator. Alias provenance still matters.
    let mut value_type = ty();
    value_type["source_aliases"][0]["span"]["file"] = json!("types.hpp");
    let value_type: CppType = serde_json::from_value(
        json!({"kind":"lvalue_reference","pointee":{"kind":"pointer","pointee":value_type}}),
    )
    .unwrap();
    value_type.validate_aliases_in(&sources).unwrap();
    assert!(
        value_type
            .validate_aliases_in(&BTreeSet::from(["fixture.cpp".into()]))
            .is_err()
    );
    let mut cyclic = ty();
    let duplicate = cyclic["source_aliases"][0].clone();
    cyclic["source_aliases"]
        .as_array_mut()
        .unwrap()
        .push(duplicate);
    let cyclic: CppType = serde_json::from_value(cyclic).unwrap();
    assert!(
        cyclic
            .validate_aliases_in(&sources)
            .unwrap_err()
            .contains("cycle")
    );
}
