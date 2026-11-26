//! The prepared lowering must enforce owned call events independently of Charon.
use super::*;
use crate::languages::rust::schema::{MirTerminator as T, OwnedArgument, Place, Span};
use crate::surface::ProgramVerificationSession;

fn fixture() -> RustExport {
    let artifact =
        include_bytes!("../../../../design/charon-trial/constructors/constructors.ullbc");
    let source = include_bytes!("../../../../design/charon-trial/constructors/lib.rs");
    let value: serde_json::Value = serde_json::from_slice(artifact).unwrap();
    let config = serde_json::from_value(value["crate_config"].clone()).unwrap();
    let sources = [("lib.rs".into(), source.to_vec())].into_iter().collect();
    let mut export = super::super::charon::decode_crate(
        artifact,
        "lib.rs",
        source,
        Some(&config),
        Some(&sources),
    )
    .unwrap();
    export
        .functions
        .retain(|f| f.name.ends_with("_default") || f.name.ends_with("_I3_new"));
    let record = export.records[0].name.clone();
    for f in &mut export.functions {
        f.parameters.push(Place {
            name: "input".into(),
            value_type: Type::Record {
                name: record.clone(),
            },
            span: Span { line: 1, column: 1 },
        });
        for block in &mut f.mir.as_mut().unwrap().blocks {
            if let T::Call {
                arguments,
                owned_arguments,
                ..
            } = &mut block.terminator
            {
                arguments.push(E::Local {
                    name: "input".into(),
                });
                owned_arguments.push(OwnedArgument {
                    index: 0,
                    local: Some("input".into()),
                    record: record.clone(),
                    moved: true,
                });
            }
        }
    }
    export
}
fn proof(export: &RustExport) -> String {
    assert_eq!(export.records[0].name, "__rust_q_I4_demo_I5_Value");
    let mut proof = String::from("verifying \"lib.rs\";\n");
    for f in &export.functions {
        let params = f
            .parameters
            .iter()
            .map(|p| format!("{}: demo::Value", p.name))
            .collect::<Vec<_>>()
            .join(", ");
        let (block, method) = if f.name.ends_with("_default") {
            ("impl Default for demo::Value", "default")
        } else {
            ("impl demo::Value", "new")
        };
        proof.push_str(&format!("{block} {{ fn {method}({params}) -> demo::Value {{ ensures result.a == 1u32; ensures result.b == 0u32; }} }}\n"));
    }
    proof
}
#[test]
fn rust_owned_parameters_check_metadata_and_consumption() {
    let original = fixture();
    let prepared = super::super::import::prepared_for_test(original.clone()).unwrap();
    ProgramVerificationSession::new_program_prepared(&proof(&original), &prepared).unwrap();
    // Each corruption breaks the call's ownership metadata. A record moved
    // twice, which the compiler never emits, is not checked: rustc decides
    // which values are live.
    for corruption in [0, 1, 2, 3, 4, 6] {
        let mut export = original.clone();
        let f = export
            .functions
            .iter_mut()
            .find(|f| f.name.ends_with("_I3_new"))
            .unwrap();
        let block = f
            .mir
            .as_mut()
            .unwrap()
            .blocks
            .iter_mut()
            .find(|b| matches!(b.terminator, T::Call { .. }))
            .unwrap();
        let T::Call {
            owned_arguments, ..
        } = &mut block.terminator
        else {
            unreachable!()
        };
        match corruption {
            0 => owned_arguments.clear(),
            1 => owned_arguments[0].index = 1,
            2 => owned_arguments[0].record = "wrong_record".into(),
            3 => owned_arguments[0].local = Some("wrong_local".into()),
            4 => owned_arguments.push(owned_arguments[0].clone()),
            6 => {
                owned_arguments[0].moved = false;
                export.records[0].destructor = Some(
                    crate::languages::rust::schema::Destructor::Explicit("forbidden_copy".into()),
                );
            }
            _ => unreachable!(),
        }
        let sidecar = proof(&export);
        match super::super::import::prepared_for_test(export) {
            Err(_) => (),
            Ok(prepared) => assert!(
                ProgramVerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
                "corruption {corruption}"
            ),
        }
    }
}
