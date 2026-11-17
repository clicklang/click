use super::*;
use serde_json::json;

pub(super) fn fixture(parameter: &str) -> RustExport {
    let span = json!({"line": 1, "column": 1});
    let ty = json!({"kind": "i32"});
    serde_json::from_value(json!({
        "schema": super::super::schema::SCHEMA,
        "compiler_commit": "test", "target": super::super::schema::TARGET,
        "edition": "2021", "overflow_checks": true, "panic": "abort",
        "mir_opt_level": 0, "logical_source": "returns.rs", "records": [],
        "functions": [
            {"name": "identity", "return_type": ty,
             "parameters": [{"name": "value", "value_type": ty, "span": span}],
             "body": [{"kind": "return", "value": {"kind": "local", "name": "value"}}],
             "mir": null, "span": span},
            {"name": "caller", "return_type": ty,
             "parameters": [{"name": parameter, "value_type": ty, "span": span}],
             "body": [{"kind": "return", "value": {"kind": "call", "function": "identity",
                       "arguments": [{"kind": "local", "name": parameter}]}}],
             "mir": null, "span": span}
        ]
    }))
    .unwrap()
}

fn operations<'a>(statement: &'a ProgramStatement, result: &mut Vec<&'a ProgramStatement>) {
    match statement {
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                operations(statement, result);
            }
        }
        ProgramStatement::Skip => (),
        statement => result.push(statement),
    }
}

#[test]
fn returned_calls_use_step_results_without_declaring_a_return_local() {
    for parameter in ["value", "__rust_return_value", "__rust_return_value_"] {
        let export = fixture(parameter);
        let (functions, _) = super::lower(&export).unwrap();
        let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
        assert_eq!(caller.parameters()[0].name(), parameter);
        let mut body = Vec::new();
        operations(
            caller.prelowered_kernel_function().unwrap().body(),
            &mut body,
        );
        assert_eq!(
            body.len(),
            2,
            "no declaration or assignment should be inserted"
        );
        assert!(
            matches!(body[0], ProgramStatement::CallResult { call: 0, function_name, .. } if function_name == "identity")
        );
        assert!(
            matches!(body[1], ProgramStatement::Return(ProgramExpression::StepResult {
            step: 0, origin: StepOrigin::Call(function), ends: true,
        }) if function == "identity")
        );
    }
}

#[test]
fn returned_calls_preserve_nested_argument_order_and_distinct_results() {
    let mut export = fixture("value");
    let mut second = export.functions[0].clone();
    second.name = "second".into();
    let mut choose = export.functions[0].clone();
    choose.name = "choose".into();
    let mut extra = choose.parameters[0].clone();
    extra.name = "ignored".into();
    choose.parameters.insert(0, extra);
    export.functions.extend([second, choose]);
    export.functions[1].body = vec![S::Return {
        value: Some(E::Call {
            function: "choose".into(),
            arguments: ["identity", "second"]
                .map(|function| E::Call {
                    function: function.into(),
                    arguments: vec![E::Local {
                        name: "value".into(),
                    }],
                })
                .into(),
        }),
    }];
    let (functions, _) = super::lower(&export).unwrap();
    let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
    let mut body = Vec::new();
    operations(
        caller.prelowered_kernel_function().unwrap().body(),
        &mut body,
    );
    let calls = body
        .iter()
        .filter_map(|statement| match statement {
            ProgramStatement::CallResult {
                call,
                function_name,
                ..
            } => Some((*call, function_name.as_str())),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, [(0, "identity"), (1, "second"), (2, "choose")]);
    assert!(
        matches!(body.last().unwrap(), ProgramStatement::Return(ProgramExpression::StepResult {
        step: 2, origin: StepOrigin::Call(function), ends: true,
    }) if function == "choose")
    );
}

#[test]
fn returned_call_results_verify_expand_and_reject_false_claims() {
    use crate::surface::{
        ProgramVerificationSession, expand_program_prepared_claim_source_by_label,
    };
    let prepared = super::super::import::prepared_for_test(fixture("value")).unwrap();
    let source = r#"verifying "returns.rs";
fn identity(value: i32) -> i32 { ensures result == value; }
fn caller(value: i32) -> i32 { ensures result == value; } by {
    step_until(function.exit);
    have call(identity, 0).result == value by solve();
}
"#;
    ProgramVerificationSession::new_program_prepared(source, &prepared).unwrap();
    let expanded =
        expand_program_prepared_claim_source_by_label(source, &prepared, "caller.contract")
            .unwrap();
    assert!(expanded.contains("call(identity, 0).result"), "{expanded}");
    assert!(!expanded.contains("__rust_return_value"), "{expanded}");
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
    let invalid = source.replace(
        "fn caller(value: i32) -> i32 { ensures result == value; }",
        "fn caller(value: i32) -> i32 { ensures result != value; }",
    );
    assert_ne!(invalid, source);
    assert!(ProgramVerificationSession::new_program_prepared(&invalid, &prepared).is_err());
}
