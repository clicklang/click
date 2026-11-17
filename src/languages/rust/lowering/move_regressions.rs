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
                 {"name": "__rust_mir_0", "value_type": {"kind": "u32"}, "span": span}
             ], "blocks": [
                 {"statements": [], "terminator": {"kind": "call",
                  "function": "read", "arguments": [], "destination": "first",
                  "target": 1}},
                 {"statements": [], "terminator": {"kind": "call",
                  "function": "read", "arguments": [], "destination": "unused",
                  "target": 2, "result": 0}},
                 {"statements": [{"kind": "assign",
                  "target": {"kind": "local", "name": "__rust_mir_0"},
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
