#[test]
fn generated_call_results_do_not_reuse_later_mir_call_identities() {
    use crate::kernel::ProgramStatement;
    use crate::languages::rust::schema::RustExport;
    use serde_json::json;
    let span = json!({"line": 1, "column": 1});
    let export: RustExport = serde_json::from_value(json!({
        "schema": super::super::schema::SCHEMA,
        "compiler_commit": "test", "target": super::super::schema::TARGET,
        "edition": "2021", "overflow_checks": true, "panic": "abort",
        "mir_opt_level": 0, "logical_source": "calls.rs", "records": [],
        "functions": [
            {"name": "read", "return_type": {"kind": "u32"},
             "parameters": [], "body": [], "mir": null, "external": true,
             "span": span},
            {"name": "caller", "return_type": {"kind": "u32"},
             "parameters": [], "body": [], "span": span,
             "mir": {"locals": [
                 {"name": "first", "value_type": {"kind": "u32"}, "span": span},
                 {"name": 0, "value_type": {"kind": "u32"}, "span": span}
             ], "blocks": [
                 {"statements": [], "terminator": {"kind": "call",
                  "function": "read", "arguments": [], "destination": "first",
                  "target": 1}},
                 {"statements": [], "terminator": {"kind": "call",
                  "function": "read", "arguments": [], "destination": "unused",
                  "target": 2, "result": 0}},
                 {"statements": [{"kind": "assign",
                  "target": {"kind": "local", "name": 0},
                  "value": {"kind": "call_result", "call": 0, "function": "read"}}],
                  "terminator": {"kind": "return"}}
             ]}}
        ]
    }))
    .unwrap();
    let (functions, _) = super::lower(&export).unwrap();
    let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
    fn collect(statement: &ProgramStatement, calls: &mut Vec<u32>) {
        match statement {
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    collect(statement, calls);
                }
            }
            ProgramStatement::CallResult { call, .. } => calls.push(*call),
            _ => {}
        }
    }
    let mut calls = Vec::new();
    collect(
        caller.prelowered_kernel_function().unwrap().body(),
        &mut calls,
    );
    assert_eq!(
        calls,
        [1, 0],
        "the generated call precedes the supplied MIR call"
    );
}

/// An operand that is a local, a literal or a borrow of a local is read
/// where its operator or call reads it: `y = x + 1` and `f(x, &mut y)`
/// declare no capture local.
#[test]
fn direct_operands_are_read_without_capture_locals() {
    use crate::languages::rust::schema::RustExport;
    use serde_json::json;
    let span = json!({"line": 1, "column": 1});
    let u32_type = json!({"kind": "u32"});
    let local = |name: &str| json!({"kind": "local", "name": name});
    let export: RustExport = serde_json::from_value(json!({
        "schema": super::super::schema::SCHEMA,
        "compiler_commit": "test", "target": super::super::schema::TARGET,
        "edition": "2021", "overflow_checks": true, "panic": "abort",
        "mir_opt_level": 0, "logical_source": "operands.rs", "records": [],
        "functions": [
            {"name": "f", "return_type": {"kind": "unit"},
             "parameters": [
                 {"name": "a", "value_type": u32_type, "span": span},
                 {"name": "b", "value_type": {"kind": "reference", "mutable": true,
                  "pointee": u32_type}, "span": span}
             ], "body": [], "mir": null, "external": true, "span": span},
            {"name": "caller", "return_type": {"kind": "unit"},
             "parameters": [{"name": "x", "value_type": u32_type, "span": span}],
             "body": [], "span": span,
             "mir": {"locals": [
                 {"name": "y", "value_type": u32_type, "span": span},
                 {"name": "unit", "value_type": {"kind": "unit"}, "span": span}
             ], "blocks": [
                 {"statements": [{"kind": "assign", "target": local("y"),
                   "value": {"kind": "binary", "operator": "add",
                    "left_type": u32_type, "right_type": u32_type,
                    "left": local("x"),
                    "right": {"kind": "unsigned_integer", "value": 1,
                              "value_type": u32_type}}}],
                  "terminator": {"kind": "call", "function": "f",
                   "arguments": [local("x"), {"kind": "borrow", "place": local("y"),
                    "value_type": {"kind": "reference", "mutable": true,
                                   "pointee": u32_type}}],
                   "destination": "unit", "target": 1}},
                 {"statements": [], "terminator": {"kind": "return"}}
             ]}}
        ]
    }))
    .unwrap();
    let (functions, _) = super::lower(&export).unwrap();
    let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
    let body = format!("{:?}", caller.prelowered_kernel_function().unwrap().body());
    assert!(!body.contains("__rust_checked"), "{body}");
}

#[test]
fn nested_enum_match_keeps_the_projection_until_its_last_test() {
    use crate::languages::rust::schema::RustExport;
    use crate::surface::ProgramVerificationSession;
    use serde_json::json;

    let span = json!({"line": 1, "column": 1});
    let inner = json!({"kind": "enum", "name": "Inner"});
    let outer = json!({"kind": "enum", "name": "Outer"});
    let export: RustExport = serde_json::from_value(json!({
        "schema": super::super::schema::SCHEMA,
        "compiler_commit": "test", "target": super::super::schema::TARGET,
        "edition": "2021", "overflow_checks": true, "panic": "abort",
        "mir_opt_level": 0, "logical_source": "nested.rs", "records": [],
        "enums": [
            {"name": "Inner", "variants": [
                {"name": "A", "fields": []},
                {"name": "B", "fields": []},
                {"name": "C", "fields": []}
            ]},
            {"name": "Outer", "generic": "Option", "arguments": [inner], "variants": [
                {"name": "None", "fields": []},
                {"name": "Some", "fields": [inner]}
            ]}
        ],
        "functions": [
            {"name": "make", "return_type": outer, "parameters": [], "body": [],
             "mir": null, "external": true, "span": span},
            {"name": "choose", "return_type": {"kind": "i32"}, "parameters": [],
             "body": [], "span": span, "mir": {"locals": [], "blocks": [
                {"statements": [], "terminator": {"kind": "call", "function": "make",
                    "arguments": [], "destination": "unused", "target": 1, "result": 0}},
                {"statements": [], "terminator": {"kind": "switch",
                    "scrutinee": {"kind": "enum_field", "name": "Outer", "variant": "Some",
                        "index": 0, "base": {"kind": "call_result", "call": 0, "function": "make"}},
                    "cases": [
                        {"label": {"kind": "variant", "name": "A"}, "target": 2},
                        {"label": {"kind": "variant", "name": "B"}, "target": 3}
                    ], "otherwise": 4}},
                {"statements": [], "terminator": {"kind": "return_value",
                    "value": {"kind": "integer", "value": 1}}},
                {"statements": [], "terminator": {"kind": "return_value",
                    "value": {"kind": "integer", "value": 2}}},
                {"statements": [], "terminator": {"kind": "return_value",
                    "value": {"kind": "integer", "value": 3}}}
             ]}}
        ]
    }))
    .unwrap();
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let source = r#"verifying "nested.rs";
extern fn make() -> Option<Inner> { ensures result == Option<Inner>::Some(Inner::B); }
fn choose() -> i32 { ensures result == 2; }
"#;
    ProgramVerificationSession::new_program_prepared(source, &prepared)
        .unwrap_or_else(|error| panic!("{}", error.report()));
}
