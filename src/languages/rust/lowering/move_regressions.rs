#[test]
fn rust_kernel_rejects_duplicate_move_drop_and_missing_cleanup() {
    use crate::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    use crate::surface::C0VerificationSession;
    let original = super::super::charon::decode(
        include_bytes!("../../../../examples/rust-move-drop/guard.ullbc"),
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
                C0VerificationSession::new_program_prepared(sidecar, &prepared).is_err(),
                "corruption {corruption}"
            ),
        }
    }
}
