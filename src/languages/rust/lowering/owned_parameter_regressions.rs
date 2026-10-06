//! The prepared lowering must enforce owned call events independently of Charon.
use super::*;
use crate::languages::rust::schema::{MirTerminator as T, OwnedArgument, Place, Span};
use crate::surface::C0VerificationSession;

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
                    local: "input".into(),
                    record: record.clone(),
                    moved: true,
                });
            }
        }
    }
    export
}
fn proof(export: &RustExport) -> String {
    let record = &export.records[0].name;
    let mut proof = String::from("verifying \"lib.rs\";\n");
    for f in &export.functions {
        let params = f
            .parameters
            .iter()
            .map(|p| format!("struct {record} {}", p.name))
            .collect::<Vec<_>>()
            .join(", ");
        proof.push_str(&format!("struct {record} {}({params}) {{ ensures result.a == 1u32; ensures result.b == 0u32; }} by {{ execute(); simp(); }}\n", f.name));
    }
    proof
}
#[test]
fn rust_owned_parameters_check_metadata_and_consumption() {
    let original = fixture();
    let prepared = super::super::import::prepared_for_test(original.clone()).unwrap();
    C0VerificationSession::new_program_prepared(&proof(&original), &prepared).unwrap();
    for corruption in 0..7 {
        let mut export = original.clone();
        if corruption == 5 {
            let f = export
                .functions
                .iter_mut()
                .find(|f| f.name.ends_with("_default"))
                .unwrap();
            let mut second = f.parameters[0].clone();
            second.name = "second".into();
            f.parameters.push(second);
        }
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
            arguments,
            owned_arguments,
            ..
        } = &mut block.terminator
        else {
            unreachable!()
        };
        match corruption {
            0 => owned_arguments.clear(),
            1 => owned_arguments[0].index = 1,
            2 => owned_arguments[0].record = "wrong_record".into(),
            3 => owned_arguments[0].local = "wrong_local".into(),
            4 => owned_arguments.push(owned_arguments[0].clone()),
            5 => {
                arguments.push(arguments[0].clone());
                let mut second = owned_arguments[0].clone();
                second.index = 1;
                owned_arguments.push(second);
            }
            6 => {
                owned_arguments[0].moved = false;
                export.records[0].destructor = Some("forbidden_copy".into());
            }
            _ => unreachable!(),
        }
        let sidecar = proof(&export);
        match super::super::import::prepared_for_test(export) {
            Err(_) => (),
            Ok(prepared) => assert!(
                C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
                "corruption {corruption}"
            ),
        }
    }
}
