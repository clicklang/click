#[test]
fn rust_kernel_rejects_duplicate_move_drop_and_missing_cleanup() {
    use crate::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    use crate::surface::ProgramVerificationSession;
    let original = super::super::charon::decode(
        include_bytes!("../../../../examples/rust-move-drop/.click/guard/guard.rs.ullbc"),
        "guard.rs",
        include_bytes!("../../../../examples/rust-move-drop/guard.rs"),
    )
    .unwrap();
    let sidecar = include_str!("../../../../examples/rust-move-drop/guard.click");
    for corruption in 0..5 {
        let mut export = original.clone();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "restore")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        let scalar_target = mir
            .locals
            .iter()
            .find(|local| local.value_type == crate::languages::rust::schema::Type::I32)
            .unwrap()
            .name
            .clone();
        if corruption == 0 || corruption == 3 || corruption == 4 {
            let statements = &mut mir
                .blocks
                .iter_mut()
                .find(|b| b.statements.iter().any(|s| matches!(s, S::Move { .. })))
                .unwrap()
                .statements;
            let index = statements
                .iter()
                .position(|s| matches!(s, S::Move { .. }))
                .unwrap();
            let extra = if corruption == 0 {
                statements[index].clone()
            } else if corruption == 4 {
                let S::Move {
                    target,
                    source,
                    record,
                } = &statements[index]
                else {
                    unreachable!()
                };
                S::Copy {
                    target: target.clone(),
                    source: source.clone(),
                    record: record.clone(),
                }
            } else {
                let S::Move { source, record, .. } = &statements[index] else {
                    unreachable!()
                };
                S::Assign {
                    target: crate::languages::rust::schema::Expression::Local {
                        name: scalar_target,
                    },
                    value: crate::languages::rust::schema::Expression::Field {
                        base: Box::new(crate::languages::rust::schema::Expression::Local {
                            name: source.clone(),
                        }),
                        record: record.clone(),
                        field: "saved".into(),
                    },
                }
            };
            statements.insert(index + 1, extra);
        } else {
            let index = mir
                .blocks
                .iter()
                .position(|b| matches!(b.terminator, T::Drop { .. }))
                .unwrap();
            let T::Drop {
                local,
                record,
                target,
            } = mir.blocks[index].terminator.clone()
            else {
                unreachable!()
            };
            if corruption == 1 {
                let duplicate = mir.blocks.len();
                mir.blocks.push(crate::languages::rust::schema::MirBlock {
                    statements: vec![],
                    terminator: T::Drop {
                        local: local.clone(),
                        record: record.clone(),
                        target,
                    },
                });
                mir.blocks[index].terminator = T::Drop {
                    local,
                    record,
                    target: duplicate,
                };
            } else {
                mir.blocks[index].terminator = T::Goto { target };
            }
        }
        match super::super::import::prepared_for_test(export) {
            Err(_) => (),
            Ok(prepared) => assert!(
                ProgramVerificationSession::new_program_prepared(sidecar, &prepared).is_err(),
                "corruption {corruption}"
            ),
        }
    }
}

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
