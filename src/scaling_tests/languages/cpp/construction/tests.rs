// Scaling tests of `src/languages/cpp/construction.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

// Many factories and fields share one helper/constructor. Rewalking that
// constructor for every factory would make this import analysis quadratic.
#[test]
fn construction_eligibility_shares_transitive_body_work() {
    for size in [8, 32, 128] {
        let span = json!({"file":"fixture.cpp", "start_line":1, "start_column":1, "end_line":1, "end_column":2});
        let integer = json!({"kind":"integer", "bits":32, "signed":true, "is_const":false, "source_aliases":[]});
        let nominal =
            json!({"kind":"record", "declaration_id":"Box", "name":"Box", "is_const":false});
        let reference = |id: &str| json!({"declaration_id":id, "name":id, "span":span});
        let place = |id: &str, ty: &serde_json::Value| json!({"declaration_id":id, "name":id, "value_type":ty, "span":span});
        let load = |id: &str| json!({"kind":"load", "place":reference(id), "value_type":integer, "span":span});
        let fields = (0..size)
            .map(|index| {
                json!({"declaration_id":format!("field_{index}"), "name":format!("field_{index}"),
            "value_type":integer, "offset_bytes":index*4, "size_bytes":4, "span":span})
            })
            .collect::<Vec<_>>();
        let record: CppRecord = serde_json::from_value(
            json!({"declaration_id":"Box", "name":"Box", "size_bytes":size*4,
            "alignment_bytes":4, "fields":fields, "destructor":null, "span":span}),
        )
        .unwrap();
        let body = fields.iter().map(|field| json!({"kind":"member_store", "object":reference("self"),
            "field":{"record_declaration_id":"Box", "declaration_id":field["declaration_id"], "name":field["name"], "span":span},
            "value":{"kind":"observer_call", "callee":reference("identity"), "arguments":[{"kind":"value", "value":load("input")}],
                "value_type":integer, "span":span}, "span":span})).collect::<Vec<_>>();
        let constructor: CppFunction = serde_json::from_value(json!({"declaration_id":"construct", "name":"construct",
            "function_kind":{"kind":"constructor", "record_declaration_id":"Box", "record_name":"Box"},
            "return_type":{"kind":"void"}, "parameters":[place("self", &json!({"kind":"lvalue_reference", "pointee":nominal})), place("input", &integer)],
            "declared_noexcept":true, "span":span, "body":body})).unwrap();
        let helper: CppFunction = serde_json::from_value(json!({"declaration_id":"identity", "name":"identity", "function_kind":{"kind":"free"},
            "return_type":integer, "parameters":[place("input", &integer)], "declared_noexcept":true, "span":span,
            "body":[{"kind":"return", "value":load("input"), "cleanups":[], "span":span}]})).unwrap();
        let factories = (0..size).map(|index| serde_json::from_value::<CppFunction>(json!({"declaration_id":format!("factory_{index}"),
            "name":format!("factory_{index}"), "function_kind":{"kind":"free"}, "return_type":nominal,
            "parameters":[place("input", &integer)], "declared_noexcept":true, "span":span,
            "body":[{"kind":"return_construct", "callee":reference("construct"), "arguments":[{"kind":"value", "value":load("input")}],
                "value_type":nominal, "cleanups":[], "span":span}]})).unwrap()).collect::<Vec<_>>();
        let functions = std::iter::once(&constructor)
            .chain(std::iter::once(&helper))
            .chain(&factories)
            .map(|function| (function.declaration_id.clone(), function))
            .collect();
        let records = RecordIndex::new(BTreeMap::from([("Box".into(), &record)]));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            validate_returns(&functions, &records)
        });
        result.unwrap();
        assert!(work >= size && work <= 16 * size + 32, "{size}: {work}");
    }
}
