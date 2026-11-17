use super::*;
use crate::surface::{ProgramVerificationSession, expand_program_prepared_claim_source_by_label};
use serde_json::{Value, json};

fn local(name: &str) -> Value {
    json!({"kind":"local", "name":name})
}
fn integer(value: i32) -> Value {
    json!({"kind":"integer", "value":value})
}
fn binary(operator: &str, ty: &str, left: Value, right: Value) -> Value {
    json!({"kind":"binary", "operator":operator, "left_type":{"kind":ty}, "right_type":{"kind":ty}, "left":left, "right":right})
}
fn returned(value: Value) -> S {
    serde_json::from_value(json!({"kind":"return", "value":value})).unwrap()
}
fn caller_body(export: &RustExport) -> ProgramStatement {
    let (functions, _) = lower(export).unwrap();
    functions
        .iter()
        .find(|f| f.name() == "caller")
        .unwrap()
        .prelowered_kernel_function()
        .unwrap()
        .body()
        .clone()
}
fn regions<'a>(statement: &'a ProgramStatement, result: &mut Vec<&'a ProgramStatement>) {
    match statement {
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                regions(statement, result);
            }
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            result.push(statement);
            regions(then_branch, result);
            regions(else_branch, result);
        }
        statement => result.push(statement),
    }
}

fn verify_expand(export: RustExport, source: &str) -> String {
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    ProgramVerificationSession::new_program_prepared(source, &prepared).unwrap();
    let expanded =
        expand_program_prepared_claim_source_by_label(source, &prepared, "caller.contract")
            .unwrap();
    assert!(!expanded.contains("__rust_checked_"), "{expanded}");
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
    expanded
}

#[test]
#[ignore = "nightly: Rust operand expansion and panic mutations"]
fn checked_operands_have_typed_results_and_raise_in_expansion() {
    let mut export = super::return_call_tests::fixture("value");
    export.functions[1].body = vec![returned(binary(
        "add",
        "i32",
        binary(
            "add",
            "i32",
            json!({"kind":"call", "function":"identity", "arguments":[local("value")]}),
            integer(1),
        ),
        integer(1),
    ))];
    let body = caller_body(&export);
    assert!(!format!("{body:?}").contains("__rust_checked_"));
    assert!(format!("{body:?}").contains("StepValue"));
    let mut numbered = Vec::new();
    regions(&body, &mut numbered);
    let capture = numbered
        .iter()
        .position(|s| matches!(s, ProgramStatement::StepValue { .. }))
        .unwrap();
    let source = format!(
        r#"verifying "returns.rs";
fn identity(value: i32) -> i32 {{ ensures result == value; }}
fn caller(value: i32) -> i32 {{ requires value >= 0; requires value < 10; ensures result == value + 2; }} by {{
    step_until(function.exit);
    have region({capture}).result == value + 1 by solve();
}}
"#
    );
    let expanded = verify_expand(export.clone(), &source);
    assert!(expanded.contains(".result"), "{expanded}");
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let invalid = source.replace("result == value + 2", "result == value + 3");
    assert!(ProgramVerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    let overflow = source.replace("value < 10", "value < 2147483647");
    assert!(ProgramVerificationSession::new_program_prepared(&overflow, &prepared).is_err());
}

#[test]
fn short_circuit_results_raise_from_the_join_and_skip_forbidden_calls() {
    for (operator, flag) in [("and", false), ("or", true)] {
        let mut export = super::return_call_tests::fixture("flag");
        export.functions[0].name = "rhs".into();
        export.functions[0].parameters.clear();
        export.functions[0].return_type = Type::Bool;
        export.functions[0].body.clear();
        export.functions[0].external = true;
        export.functions[1].parameters[0].value_type = Type::Bool;
        export.functions[1].return_type = Type::Bool;
        export.functions[1].body = vec![returned(binary(
            operator,
            "bool",
            local("flag"),
            json!({"kind":"call", "function":"rhs", "arguments":[]}),
        ))];
        let body = caller_body(&export);
        let mut numbered = Vec::new();
        regions(&body, &mut numbered);
        let join = numbered
            .iter()
            .position(|s| matches!(s, ProgramStatement::If { .. }))
            .unwrap();
        let source = format!(
            r#"verifying "returns.rs";
extern fn rhs() -> bool {{ requires false; ensures result == true; }}
fn caller(flag: bool) -> bool {{ requires flag == {flag}; ensures result == {flag}; }} by {{
    step_until(function.exit);
    have region({join}).result == {flag} by solve();
}}
"#
        );
        verify_expand(export.clone(), &source);
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let invalid = source.replace(
            &format!("requires flag == {flag}"),
            &format!("requires flag == {}", !flag),
        );
        assert!(ProgramVerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

#[test]
fn operand_capture_keeps_the_read_before_a_mutating_call() {
    let mut export = super::return_call_tests::fixture("unused");
    let span = json!({"line":1,"column":1});
    export.functions[0] = serde_json::from_value(json!({
        "name":"bump", "return_type":{"kind":"i32"},
        "parameters":[{"name":"target", "value_type":{"kind":"reference", "mutable":true, "pointee":{"kind":"i32"}}, "span":span}],
        "body":[{"kind":"assign", "target":{"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}}, "value":integer(9)},
                {"kind":"return", "value":integer(2)}], "mir":null, "span":span
    })).unwrap();
    export.functions[1].parameters = export.functions[0].parameters.clone();
    export.functions[1].body = vec![returned(binary(
        "add",
        "i32",
        json!({"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}}),
        json!({"kind":"call", "function":"bump", "arguments":[local("target")]}),
    ))];
    verify_expand(
        export,
        r#"verifying "returns.rs";
fn bump(target: &mut i32) -> i32 { owns *target; ensures *target == 9; ensures result == 2; }
fn caller(target: &mut i32) -> i32 { owns *target; requires *target == 1; ensures *target == 9; ensures result == 3; } by { step_until(function.exit); solve(); }
"#,
    );
}

#[test]
#[ignore = "nightly: Rust array-repeat expansion"]
fn array_repeat_evaluates_its_operand_once_including_zero_elements() {
    for length in [0, 3] {
        let mut export = super::return_call_tests::fixture("unused");
        let span = json!({"line":1,"column":1});
        let deref =
            json!({"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}});
        export.functions[0] = serde_json::from_value(json!({
            "name":"tick", "return_type":{"kind":"i32"},
            "parameters":[{"name":"target", "value_type":{"kind":"reference", "mutable":true, "pointee":{"kind":"i32"}}, "span":span}],
            "body":[{"kind":"assign", "target":deref, "value":binary("add", "i32", deref.clone(), integer(1))},
                    {"kind":"return", "value":integer(2)}], "mir":null, "span":span
        })).unwrap();
        export.functions[1].parameters = export.functions[0].parameters.clone();
        export.functions[1].body = vec![
            serde_json::from_value(json!({"kind":"declare", "place":{"name":"items", "value_type":{"kind":"array", "element":{"kind":"i32"}, "length":length}, "span":span},
                "initializer":{"kind":"repeat", "length":length, "value":{"kind":"call", "function":"tick", "arguments":[local("target")]}}})).unwrap(),
            returned(deref),
        ];
        verify_expand(
            export,
            r#"verifying "returns.rs";
fn tick(target: &mut i32) -> i32 { owns *target; requires *target >= 0; requires *target < 10; ensures *target == old(*target) + 1; ensures result == 2; }
fn caller(target: &mut i32) -> i32 { owns *target; requires *target == 1; ensures *target == 2; ensures result == 2; } by { step_until(function.exit); solve(); }
"#,
        );
    }
}

#[test]
fn former_checked_variable_spelling_remains_a_valid_source_parameter() {
    let name = "__rust_checked_0";
    let mut export = super::return_call_tests::fixture(name);
    export.functions[1].body = vec![returned(binary(
        "add",
        "i32",
        binary("add", "i32", local(name), integer(1)),
        integer(1),
    ))];
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let source = r#"verifying "returns.rs";
fn identity(value: i32) -> i32 { ensures result == value; }
fn caller(__rust_checked_0: i32) -> i32 { requires __rust_checked_0 >= 0; requires __rust_checked_0 < 10; ensures result == __rust_checked_0 + 2; }
"#;
    ProgramVerificationSession::new_program_prepared(source, &prepared).unwrap();
    let expanded =
        expand_program_prepared_claim_source_by_label(source, &prepared, "caller.ensures_0")
            .unwrap();
    assert!(expanded.contains(name));
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
}
