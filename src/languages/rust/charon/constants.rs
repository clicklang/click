//! Scalar constants execute their checked initializer CFG, never a value summary.
use super::*;

fn scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool | Type::I32 | Type::U8 | Type::U16 | Type::U32 | Type::Usize
    )
}

// The first constant subset has no calls, references, or dependencies. Its
// ordinary scalar arithmetic keeps the same overflow/definedness obligations
// as function bodies. Restrict reads too, so a corrupted initializer cannot
// smuggle in a recursive global evaluation.
fn initializer_operand(operand: &a::Operand) -> Result<(), String> {
    match operand {
        a::Operand::Copy(place) | a::Operand::Move(place)
            if matches!(place.kind, a::PlaceKind::Local(_)) =>
        {
            Ok(())
        }
        a::Operand::Const(value) => match (value.kind(), value.ty().kind()) {
            (a::ConstantExprKind::Bool(_), a::TyKind::Scalar(a::ScalarTy::Bool)) => Ok(()),
            (
                a::ConstantExprKind::Integer(integer),
                a::TyKind::Scalar(a::ScalarTy::Integer(ty)),
            ) if integer.ty() == *ty => Ok(()),
            _ => Err(unsupported("constant initializer literal type")),
        },
        _ => Err(unsupported(
            "constant initializer dependency or nonlocal operand",
        )),
    }
}

impl Adapter<'_> {
    pub(super) fn constant_initializer_name(
        &self,
        id: a::FunDeclId,
        f: &a::FunDecl,
        reference: &a::GlobalDeclRef,
    ) -> Result<String, String> {
        if !self.crate_mode {
            return Err(unsupported(
                "local constant/global initializer outside crate imports",
            ));
        }
        let global = self
            .krate
            .global_decls
            .get(reference.id)
            .ok_or_else(|| unsupported("missing constant declaration"))?;
        let a::ConstantExprKind::Call(pointer, arguments) = global.value.kind() else {
            return Err(unsupported("constant initializer linkage"));
        };
        if global.def_id != reference.id
            || !reference.generics.is_empty()
            || !global.item_meta.is_local
            || !matches!(global.global_kind, a::GlobalKind::NamedConst)
            || !matches!(global.src, a::GlobalSource::Normal)
            || !global.generics.is_empty()
            || !scalar(&self.ty(&global.ty)?)
            || global.value.ty() != &global.ty
            || !matches!(pointer.kind.as_ref(), a::FnPtrKind::Fun(actual) if *actual == id)
            || !pointer.generics.is_empty()
            || !arguments.is_empty()
            || f.def_id != id
            || f.item_meta.name != global.item_meta.name
            || !f.generics.is_empty()
            || !f.signature.inputs.is_empty()
            || f.signature.output != global.ty
            || f.signature.is_unsafe
            || f.signature.is_variadic
            || f.signature.abi != a::Abi::Rust
        {
            return Err(unsupported(
                "scalar constant declaration/initializer identity",
            ));
        }
        let a::Body::Unstructured(body) = &f.body else {
            return Err(unsupported("missing constant initializer CFG"));
        };
        if body.locals.arg_count != 0 {
            return Err(unsupported("constant initializer parameters"));
        }
        for local in &body.locals.locals {
            if !scalar(&self.ty(&local.ty)?) {
                return Err(unsupported("nonscalar constant initializer local"));
            }
        }
        for block in &body.body {
            for statement in &block.statements {
                match &statement.kind {
                    u::StatementKind::Assign(place, value)
                        if matches!(place.kind, a::PlaceKind::Local(_)) =>
                    {
                        match value {
                            a::Rvalue::Use(operand, _) | a::Rvalue::UnaryOp(_, operand) => {
                                initializer_operand(operand)?
                            }
                            a::Rvalue::BinaryOp(_, left, right) => {
                                initializer_operand(left)?;
                                initializer_operand(right)?;
                            }
                            _ => return Err(unsupported("nonarithmetic constant initializer")),
                        }
                    }
                    u::StatementKind::StorageLive(_)
                    | u::StatementKind::StorageDead(_)
                    | u::StatementKind::Nop => {}
                    _ => return Err(unsupported("constant initializer effects")),
                }
            }
            if !matches!(block.terminator.kind, u::TerminatorKind::Return) {
                return Err(unsupported("constant initializer control flow or calls"));
            }
        }
        self.qualified_function_name(&global.item_meta.name)
    }

    pub(super) fn constant_read(
        &self,
        reference: &a::GlobalDeclRef,
        ty: &a::Ty,
    ) -> Result<E, String> {
        let global = self
            .krate
            .global_decls
            .get(reference.id)
            .ok_or_else(|| unsupported("missing constant declaration"))?;
        let id = global
            .init_fun_id()
            .ok_or_else(|| unsupported("constant initializer linkage"))?;
        let f = self
            .krate
            .fun_decls
            .get(id)
            .ok_or_else(|| unsupported("missing constant initializer"))?;
        let a::FunSource::GlobalInitializer(actual) = &f.src else {
            return Err(unsupported("constant initializer source"));
        };
        if actual.id != reference.id || ty != &global.ty || !reference.generics.is_empty() {
            return Err(unsupported("constant read identity/type"));
        }
        // Registration checked the body once. Reads check the declared link
        // and use its registered identity without rescanning the initializer.
        if !self.crate_mode || !actual.generics.is_empty() {
            return Err(unsupported("constant read outside checked crate profile"));
        }
        let name = self
            .functions
            .get(&id)
            .ok_or_else(|| unsupported("unregistered constant initializer"))?;
        Ok(E::Call {
            function: name.clone(),
            arguments: vec![],
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ARTIFACT: &[u8] =
        include_bytes!("../../../../design/charon-trial/scalar-constants/constants.ullbc");
    const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/scalar-constants/lib.rs");
    fn decode(artifact: &TrialArtifact) -> Result<out::RustExport, String> {
        let sources = [("lib.rs".into(), SOURCE.to_vec())].into_iter().collect();
        decode_crate(
            &serde_json::to_vec(artifact).unwrap(),
            "lib.rs",
            SOURCE,
            artifact.crate_config.as_ref(),
            Some(&sources),
        )
    }
    const PROOF: &str = "verifying \"lib.rs\"; uint64 __rust_q_I4_demo_I5_entry_I10_CHUNK_SIZE() { ensures result == 22208u64; } by { execute(); simp(); } uint64 __rust_q_I4_demo_I5_entry() { ensures result == 22208u64; } by { execute(); simp(); }";

    #[test]
    fn charon_constants_verify_bodies_and_reject_assumed_values() {
        let artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let export = decode(&artifact).unwrap();
        let prepared = super::super::super::import::prepared_for_test(export.clone()).unwrap();
        crate::surface::C0VerificationSession::new_program_prepared(PROOF, &prepared).unwrap();
        assert!(
            crate::surface::C0VerificationSession::new_program_prepared(
                &PROOF.replace("22208u64", "22209u64"),
                &prepared
            )
            .is_err()
        );
        // Removing the real initializer must invalidate its value proof.
        let mut changed = export;
        let initializer = changed
            .functions
            .iter_mut()
            .find(|f| f.name.ends_with("_I10_CHUNK_SIZE"))
            .unwrap();
        for block in &mut initializer.mir.as_mut().unwrap().blocks {
            block.statements.clear();
        }
        let prepared = super::super::super::import::prepared_for_test(changed).unwrap();
        assert!(
            crate::surface::C0VerificationSession::new_program_prepared(PROOF, &prepared).is_err()
        );
        let mut overflowing: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let f = &mut overflowing.data.translated.fun_decls[a::FunDeclId::from(8)];
        let a::Body::Unstructured(body) = &mut f.body else {
            panic!()
        };
        let left = body.body[0]
            .statements
            .iter_mut()
            .find_map(|s| {
                if let u::StatementKind::Assign(_, a::Rvalue::BinaryOp(_, left, _)) = &mut s.kind {
                    Some(left)
                } else {
                    None
                }
            })
            .unwrap();
        *left = a::Operand::Const(a::ConstantExpr::mk_usize(u64::MAX.into()));
        let prepared =
            super::super::super::import::prepared_for_test(decode(&overflowing).unwrap()).unwrap();
        assert!(
            crate::surface::C0VerificationSession::new_program_prepared(PROOF, &prepared).is_err()
        );
    }

    #[test]
    fn charon_constants_reject_corrupt_identity_effects_and_cycles() {
        for mutation in 0..14 {
            let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let krate = &mut artifact.data.translated;
            let global_id = a::GlobalDeclId::from(2);
            let function_id = krate.global_decls[global_id].init_fun_id().unwrap();
            let ty = krate.global_decls[global_id].ty.clone();
            match mutation {
                0 => {
                    krate.global_decls[global_id].global_kind = a::GlobalKind::Static {
                        is_mut: false,
                        is_safe: true,
                        is_thread_local: false,
                    }
                }
                1 => krate.global_decls[global_id].global_kind = a::GlobalKind::AnonConst,
                2 => krate.global_decls[global_id].ty = a::Ty::mk_unit(),
                3 => krate.global_decls[global_id].item_meta.is_local = false,
                4 => krate.global_decls[global_id]
                    .value
                    .with_contents_mut(|kind, _| {
                        let a::ConstantExprKind::Call(pointer, _) = kind else {
                            panic!()
                        };
                        *pointer.kind = a::FnPtrKind::Fun(a::FunDeclId::from(0));
                    }),
                5 => krate.fun_decls[function_id].signature.inputs.push(ty),
                6 => krate.fun_decls[function_id].signature.is_unsafe = true,
                7 => krate.fun_decls[function_id].signature.output = a::Ty::mk_unit(),
                8 => {
                    krate.fun_decls[function_id].item_meta.name = krate.fun_decls
                        [a::FunDeclId::from(0)]
                    .item_meta
                    .name
                    .clone()
                }
                9 => {
                    let a::FunSource::GlobalInitializer(reference) =
                        &mut krate.fun_decls[function_id].src
                    else {
                        panic!()
                    };
                    reference.id = a::GlobalDeclId::from(0);
                }
                10 | 11 => {
                    let a::FunSource::GlobalInitializer(reference) =
                        &krate.fun_decls[function_id].src
                    else {
                        panic!()
                    };
                    let reference = reference.clone();
                    let a::Body::Unstructured(body) = &mut krate.fun_decls[function_id].body else {
                        panic!()
                    };
                    if mutation == 10 {
                        body.body[0].terminator.kind = u::TerminatorKind::Goto {
                            target: u::BlockId::from(0),
                        };
                    } else {
                        let statement = body.body[0]
                            .statements
                            .iter_mut()
                            .find(|s| matches!(s.kind, u::StatementKind::Assign(..)))
                            .unwrap();
                        let u::StatementKind::Assign(_, value) = &mut statement.kind else {
                            panic!()
                        };
                        *value = a::Rvalue::Use(
                            a::Operand::Copy(a::Place {
                                kind: a::PlaceKind::Global(reference),
                                ty,
                            }),
                            a::WithRetag::No,
                        );
                    }
                }
                12 => {
                    let a::Body::Unstructured(body) =
                        &mut krate.fun_decls[a::FunDeclId::from(2)].body
                    else {
                        panic!()
                    };
                    let read = body.body[0]
                        .statements
                        .iter_mut()
                        .find_map(|s| {
                            if let u::StatementKind::Assign(
                                _,
                                a::Rvalue::Use(a::Operand::Copy(place), _),
                            ) = &mut s.kind
                            {
                                Some(place)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    read.ty = a::Ty::mk_unit();
                }
                13 => {
                    let a::Body::Unstructured(body) = &mut krate.fun_decls[function_id].body else {
                        panic!()
                    };
                    let left = body.body[0]
                        .statements
                        .iter_mut()
                        .find_map(|s| {
                            if let u::StatementKind::Assign(_, a::Rvalue::BinaryOp(_, left, _)) =
                                &mut s.kind
                            {
                                Some(left)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    *left = a::Operand::Const(a::ConstantExpr::new(
                        a::ConstantExprKind::Bool(true),
                        ty,
                    ));
                }
                _ => unreachable!(),
            }
            assert!(decode(&artifact).is_err(), "constant mutation {mutation}");
        }
    }
}
