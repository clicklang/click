//! Concrete Default dispatch authorizes importing a body, never a value summary.
use super::*;

impl Adapter<'_> {
    pub(super) fn is_default_method(&self, f: &a::FunDecl) -> bool {
        let a::FunSource::TraitImpl { trait_ref, .. } = &f.src else {
            return false;
        };
        self.krate
            .trait_decls
            .get(trait_ref.id)
            .is_some_and(|tr| tr.item_meta.diagnostic_item.as_deref() == Some("Default"))
    }

    pub(super) fn default_constructor_name(&self, f: &a::FunDecl) -> Result<String, String> {
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &f.src
        else {
            return Err(unsupported("Default constructor source"));
        };
        let tr = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing Default trait"))?;
        let imp = self
            .krate
            .trait_impls
            .get(impl_ref.id)
            .ok_or_else(|| unsupported("missing Default implementation"))?;
        let method = tr
            .methods
            .get(*item_id)
            .ok_or_else(|| unsupported("missing Default method"))?;
        if !self.crate_mode
            || tr.item_meta.is_local
            || tr.is_unsafe
            || tr.item_meta.diagnostic_item.as_deref() != Some("Default")
            || !protocol::path(&tr.item_meta.name, &["core", "default", "Default"])
            || !matches!(tr.src, a::TraitDeclSource::Normal)
            || tr.generics.types.len() != 1
            || !tr.generics.regions.is_empty()
            || !tr.generics.const_generics.is_empty()
            || !tr.consts.is_empty()
            || !tr.types.is_empty()
            || tr.methods.iter().take(2).count() != 1
            || item_id.index() != 0
            || !method.params.is_empty()
            || method.skip_binder.name.0 != "default"
            || method.skip_binder.item_meta.diagnostic_item.as_deref() != Some("default_fn")
            || !protocol::path(
                &method.skip_binder.item_meta.name,
                &["core", "default", "Default", "default"],
            )
            || !method.skip_binder.signature.inputs.is_empty()
            || !matches!(method.skip_binder.signature.output.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 1 && id.index() == 0)
            || method.skip_binder.signature.is_unsafe
            || method.skip_binder.signature.is_variadic
            || method.skip_binder.signature.abi != a::Abi::Rust
            || !imp.item_meta.is_local
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || !imp.generics.is_empty()
            || !impl_ref.generics.is_empty()
            || imp.impl_trait.id != trait_ref.id
            || imp.impl_trait.generics.types.len() != 1
            || !imp.impl_trait.generics.regions.is_empty()
            || !imp.impl_trait.generics.const_generics.is_empty()
            || !imp.impl_trait.generics.trait_refs.is_empty()
            || imp.methods.iter().take(2).count() != 1
            || imp.methods.get(*item_id).is_none_or(|m| {
                !m.params.is_empty()
                    || m.skip_binder.id != f.def_id
                    || !m.skip_binder.generics.is_empty()
            })
            || !f.item_meta.is_local
            || !matches!(f.body, a::Body::Unstructured(_))
            || !f.generics.is_empty()
            || !f.signature.inputs.is_empty()
            || f.signature.is_unsafe
            || f.signature.is_variadic
            || f.signature.abi != a::Abi::Rust
            || !local_impl_method_path(
                &f.item_meta.name,
                &self.krate.crate_name,
                impl_ref.id,
                "default",
            )
            || f.item_meta.name.name[..f.item_meta.name.name.len() - 1] != imp.item_meta.name.name
            || trait_ref.generics.types.len() != 1
            || !trait_ref.generics.regions.is_empty()
            || !trait_ref.generics.const_generics.is_empty()
            || !trait_ref.generics.trait_refs.is_empty()
        {
            return Err(unsupported("Default declaration/implementation identity"));
        }
        let record = self.record_id(&imp.impl_trait.generics.types[0])?;
        self.ty(&imp.impl_trait.generics.types[0])?;
        if f.signature.output != imp.impl_trait.generics.types[0]
            || trait_ref.generics.types[0] != f.signature.output
        {
            return Err(unsupported("Default return/receiver type"));
        }
        Ok(format!("{}_default", self.records[&record]))
    }

    pub(super) fn default_constructor_call(
        &self,
        callee: &a::FunDecl,
        ptr: &a::FnPtr,
        call: &a::Call,
    ) -> Result<(), String> {
        if !self.is_default_method(callee) {
            return Ok(());
        }
        self.default_constructor_name(callee)?;
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            unreachable!();
        };
        if call.safety == a::CallSafety::Unsafe
            || !call.args.is_empty()
            || !ptr.generics.is_empty()
            || call.dest.ty != callee.signature.output
        {
            return Err(unsupported("Default call signature"));
        }
        if let a::FnPtrKind::Trait(reference, method) = ptr.kind.as_ref() {
            let decl = &reference.trait_decl_ref.skip_binder;
            if *method != *item_id
                || !reference.trait_decl_ref.regions.is_empty()
                || decl.id != trait_ref.id
                || !matches!(&reference.kind, a::TraitRefKind::TraitImpl(r) if r.id == impl_ref.id && r.generics.is_empty())
                || decl.generics.types.len() != 1
                || decl.generics.types[0] != callee.signature.output
                || !decl.generics.regions.is_empty()
                || !decl.generics.const_generics.is_empty()
                || !decl.generics.trait_refs.is_empty()
            {
                return Err(unsupported("Default resolved trait dispatch"));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ARTIFACT: &[u8] =
        include_bytes!("../../../../design/charon-trial/constructors/constructors.ullbc");
    const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/constructors/lib.rs");
    fn decode_fixture(artifact: &TrialArtifact) -> Result<out::RustExport, String> {
        let sources = [("lib.rs".into(), SOURCE.to_vec())].into_iter().collect();
        decode_crate(
            &serde_json::to_vec(artifact).unwrap(),
            "lib.rs",
            SOURCE,
            artifact.crate_config.as_ref(),
            Some(&sources),
        )
    }
    #[test]
    fn charon_default_executes_body_and_checks_resolved_identity() {
        let artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let export = decode_fixture(&artifact).unwrap();
        let prepared = super::super::super::import::prepared_for_test(export).unwrap();
        let proof = "verifying \"lib.rs\"; struct __rust_q_I4_demo_I5_Value __rust_q_I4_demo_I5_Value_default() { ensures result.a == 1u32; ensures result.b == 0u32; } by { execute(); simp(); } struct __rust_q_I4_demo_I5_Value __rust_q_I4_demo_T25___rust_q_I4_demo_I5_Value_I3_new() { ensures result.a == 1u32; ensures result.b == 0u32; } by { execute(); simp(); } uint32 __rust_q_I4_demo_I5_entry() { ensures result == 1u32; } by { execute(); simp(); }";
        crate::surface::C0VerificationSession::new_program_prepared(proof, &prepared).unwrap();
        assert!(
            crate::surface::C0VerificationSession::new_program_prepared(
                &proof.replace("1u32", "0u32"),
                &prepared
            )
            .is_err()
        );
        for mutation in 0..2 {
            let artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let mut export = decode_fixture(&artifact).unwrap();
            if mutation == 0 {
                let f = export
                    .functions
                    .iter_mut()
                    .find(|f| f.name.ends_with("_default"))
                    .unwrap();
                for block in &mut f.mir.as_mut().unwrap().blocks {
                    block.statements.clear();
                }
            } else {
                let f = export
                    .functions
                    .iter_mut()
                    .find(|f| f.name.ends_with("_I3_new"))
                    .unwrap();
                let mir = f.mir.as_mut().unwrap();
                let index = mir.blocks.len();
                let block = mir
                    .blocks
                    .iter_mut()
                    .find(|b| matches!(b.terminator, T::Call { .. }))
                    .unwrap();
                let repeat = block.terminator.clone();
                let T::Call { target, .. } = &mut block.terminator else {
                    unreachable!();
                };
                *target = index;
                mir.blocks.push(out::MirBlock {
                    statements: vec![],
                    terminator: repeat,
                });
            }
            let prepared = super::super::super::import::prepared_for_test(export).unwrap();
            assert!(
                crate::surface::C0VerificationSession::new_program_prepared(proof, &prepared)
                    .is_err(),
                "ownership mutation {mutation}"
            );
        }
        for mutation in 0..13 {
            let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let k = &mut artifact.data.translated;
            let trait_id = k
                .trait_decls
                .iter()
                .find(|t| t.item_meta.diagnostic_item.as_deref() == Some("Default"))
                .unwrap()
                .def_id;
            let impl_id = k
                .trait_impls
                .iter()
                .find(|i| i.impl_trait.id == trait_id)
                .unwrap()
                .def_id;
            let function_id = k.trait_impls[impl_id]
                .methods
                .iter()
                .next()
                .unwrap()
                .skip_binder
                .id;
            match mutation {
                0 => k.trait_decls[trait_id].item_meta.is_local = true,
                1 => k.trait_decls[trait_id].item_meta.diagnostic_item = None,
                2 => {
                    k.trait_decls[trait_id]
                        .methods
                        .iter_mut()
                        .next()
                        .unwrap()
                        .skip_binder
                        .signature
                        .is_unsafe = true
                }
                3 => {
                    k.trait_decls[trait_id]
                        .methods
                        .iter_mut()
                        .next()
                        .unwrap()
                        .skip_binder
                        .item_meta
                        .diagnostic_item = None
                }
                4 => k.trait_impls[impl_id].is_negative = true,
                5 => {
                    k.trait_impls[impl_id]
                        .methods
                        .iter_mut()
                        .next()
                        .unwrap()
                        .skip_binder
                        .id = a::FunDeclId::from(0)
                }
                6 => k.fun_decls[function_id].signature.is_unsafe = true,
                7 => k.fun_decls[function_id].signature.output = a::Ty::mk_unit(),
                8 => k.trait_impls[impl_id].impl_trait.generics.types.clear(),
                9 => artifact.crate_profile = Some("click-charon-crate-v1".into()),
                12 => artifact.crate_profile = Some("click-charon-crate-v2".into()),
                10 | 11 => {
                    let output = k.fun_decls[function_id].signature.output.clone();
                    let f = k
                        .fun_decls
                        .iter_mut()
                        .find(|f| {
                            matches!(f.src, a::FunSource::Normal)
                                && f.signature.inputs.is_empty()
                                && f.signature.output == output
                        })
                        .unwrap();
                    let a::Body::Unstructured(body) = &mut f.body else {
                        unreachable!();
                    };
                    let call = body
                        .body
                        .iter_mut()
                        .find_map(|block| {
                            if let u::TerminatorKind::Call { call, .. } = &mut block.terminator.kind
                            {
                                Some(call)
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    if mutation == 10 {
                        call.dest.ty = a::Ty::mk_unit();
                    } else {
                        call.safety = a::CallSafety::Unsafe;
                    }
                }
                _ => unreachable!(),
            }
            assert!(decode_fixture(&artifact).is_err(), "mutation {mutation}");
        }
    }
}
