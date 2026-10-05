//! Compiler-resolved shared byte ChunksExact protocol.
use super::protocol::{local, operand_place, path, variable};
use super::*;
fn shared_slice(ty: &a::Ty, template: bool) -> bool {
    matches!(ty.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Shared)
        if matches!(pointee.kind(), a::TyKind::Slice(element, _) if if template { variable(element) } else { byte_slice(pointee) }))
}
impl Adapter<'_> {
    pub(super) fn chunk_adt(&self, ty: &a::Ty, template: bool) -> bool {
        let a::TyKind::Adt(r) = ty.kind() else {
            return false;
        };
        let Some(decl) = self.krate.type_decls.get(r.id) else {
            return false;
        };
        !decl.item_meta.is_local
            && path(
                &decl.item_meta.name,
                &["core", "slice", "iter", "ChunksExact"],
            )
            && matches!(decl.src, a::TypeSource::Normal)
            && matches!(decl.kind, a::TypeDeclKind::Opaque)
            && decl.generics.regions.len() == 1
            && r.generics.regions.len() == 1
            && decl.generics.types.len() == 1
            && decl.generics.const_generics.is_empty()
            && r.generics.types.len() == 1
            && r.generics.const_generics.is_empty()
            && if template {
                variable(&r.generics.types[0])
            } else {
                matches!(self.ty(&r.generics.types[0]), Ok(Type::U8))
            }
    }
    pub(super) fn chunk_type(&self, ty: &a::Ty) -> bool {
        self.chunk_adt(ty, false)
    }
    fn option_adt(&self, ty: &a::Ty, template: bool) -> bool {
        let a::TyKind::Adt(r) = ty.kind() else {
            return false;
        };
        let Some(decl) = self.krate.type_decls.get(r.id) else {
            return false;
        };
        !decl.item_meta.is_local
            && decl.item_meta.lang_item == Some(LangItem::Option)
            && path(&decl.item_meta.name, &["core", "option", "Option"])
            && matches!(decl.src, a::TypeSource::Normal)
            && matches!(decl.kind, a::TypeDeclKind::Opaque)
            && decl.generics.regions.is_empty()
            && decl.generics.types.len() == 1
            && decl.generics.const_generics.is_empty()
            && r.generics.regions.is_empty()
            && r.generics.types.len() == 1
            && r.generics.const_generics.is_empty()
            && shared_slice(&r.generics.types[0], template)
    }
    pub(super) fn chunk_option_type(&self, ty: &a::Ty) -> bool {
        self.option_adt(ty, false)
    }
    fn chunk_reference(&self, ty: &a::Ty) -> Option<bool> {
        match ty.kind() {
            a::TyKind::Ref(_, p, kind) if self.chunk_type(p) => Some(*kind == a::RefKind::Mut),
            _ => None,
        }
    }
}
impl BodyAdapter<'_, '_> {
    pub(super) fn chunk_call(&self, terminator: &u::Terminator) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &terminator.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let callee = &self.adapter.krate.fun_decls[self.adapter.resolve(ptr)?];
        let relevant = self.adapter.chunk_type(&call.dest.ty)
            || self.adapter.chunk_option_type(&call.dest.ty)
            || call
                .args
                .iter()
                .any(|op| self.adapter.chunk_reference(op.ty()).is_some());
        if !relevant {
            return Ok(None);
        }
        if callee.item_meta.is_local
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || callee.generics.types.len() != 1
            || !callee.generics.const_generics.is_empty()
            || ptr.generics.types.len() != 1
            || !ptr.generics.const_generics.is_empty()
        {
            return Err(unsupported("chunk model declaration/type mismatch"));
        }
        let elements = &callee.item_meta.name.name;
        let method = match elements.last() {
            Some(a::PathElem::Ident(name, d)) if *d == a::Disambiguator::ZERO => name.as_str(),
            _ => return Err(unsupported("chunk model method identity")),
        };
        let destination = self.local(local(&call.dest)?)?;
        match (&callee.src, method) {
            (a::FunSource::Normal, "chunks_exact" | "remainder") => {
                let prefix: &[&str] = if method == "chunks_exact" {
                    &["core", "slice"]
                } else {
                    &["core", "slice", "iter"]
                };
                if elements.len() != prefix.len() + 2 || !elements[..prefix.len()].iter().zip(prefix).all(|(part, expected)| matches!(part, a::PathElem::Ident(actual, d) if actual == expected && *d == a::Disambiguator::ZERO)) { return Err(unsupported("chunk inherent method identity")) }
                let a::PathElem::Impl(a::ImplElem::Ty(receiver)) = &elements[prefix.len()] else {
                    return Err(unsupported("chunk inherent receiver"));
                };
                if self.adapter.ty(&ptr.generics.types[0])? != Type::U8 {
                    return Err(unsupported("chunk element instantiation"));
                }
                if method == "chunks_exact" {
                    if !matches!(receiver.skip_binder.kind(), a::TyKind::Slice(element, _) if variable(element))
                        || !matches!(callee.signature.inputs.as_slice(), [slice, size] if shared_slice(slice, true) && self.adapter.ty(size).ok() == Some(Type::Usize))
                        || !self.adapter.chunk_adt(&callee.signature.output, true)
                        || !self.adapter.chunk_type(&call.dest.ty)
                    {
                        return Err(unsupported("chunks_exact signature"));
                    }
                    let [slice, size] = call.args.as_slice() else {
                        return Err(unsupported("chunks_exact arity"));
                    };
                    if !shared_slice(slice.ty(), false)
                        || self.adapter.ty(size.ty())? != Type::Usize
                    {
                        return Err(unsupported("chunks_exact argument types"));
                    }
                    Ok(Some(S::ChunkInitialize {
                        target: destination,
                        slice: self.operand(slice)?,
                        size: self.operand(size)?,
                    }))
                } else {
                    if !self.adapter.chunk_adt(&receiver.skip_binder, true)
                        || !matches!(callee.signature.inputs.as_slice(), [reference] if matches!(reference.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if self.adapter.chunk_adt(p, true)))
                        || !shared_slice(&callee.signature.output, true)
                        || !shared_slice(&call.dest.ty, false)
                    {
                        return Err(unsupported("chunk remainder signature"));
                    }
                    let [argument] = call.args.as_slice() else {
                        return Err(unsupported("chunk remainder arity"));
                    };
                    if self.adapter.chunk_reference(argument.ty()) != Some(false) {
                        return Err(unsupported("chunk remainder receiver type"));
                    }
                    Ok(Some(S::Assign {
                        target: E::Local { name: destination },
                        value: E::ChunkRemainder {
                            iterator: self.iterator_root(operand_place(argument)?)?,
                        },
                    }))
                }
            }
            (
                a::FunSource::TraitImpl {
                    trait_ref,
                    impl_ref,
                    item_id,
                    ..
                },
                "next" | "into_iter",
            ) => {
                let tr = &self.adapter.krate.trait_decls[trait_ref.id];
                let imp = &self.adapter.krate.trait_impls[impl_ref.id];
                if tr.item_meta.is_local
                    || imp.item_meta.is_local
                    || elements[..elements.len() - 1] != imp.item_meta.name.name
                    || imp.is_unsafe
                    || imp.is_negative
                    || !matches!(imp.src, a::TraitImplSource::Normal)
                    || imp.impl_trait.id != trait_ref.id
                    || imp.impl_trait.generics.types.len() != 1
                    || !imp.impl_trait.generics.const_generics.is_empty()
                    || tr
                        .methods
                        .get(*item_id)
                        .is_none_or(|declaration| declaration.skip_binder.name.0 != method)
                    || item_id.index() != 0
                    || tr.item_meta.diagnostic_item.as_deref()
                        != Some(if method == "next" {
                            "Iterator"
                        } else {
                            "IntoIterator"
                        })
                    || imp
                        .methods
                        .get(*item_id)
                        .is_none_or(|definition| definition.skip_binder.id != callee.def_id)
                {
                    return Err(unsupported("chunk trait/implementation identity"));
                }
                let [argument] = call.args.as_slice() else {
                    return Err(unsupported("chunk protocol arity"));
                };
                if method == "into_iter" {
                    if !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "collect", "IntoIterator"],
                    ) || !variable(&imp.impl_trait.generics.types[0])
                        || !variable(&callee.signature.output)
                        || !matches!(callee.signature.inputs.as_slice(), [input] if variable(input))
                        || !self.adapter.chunk_type(&ptr.generics.types[0])
                        || !self.adapter.chunk_type(argument.ty())
                        || !self.adapter.chunk_type(&call.dest.ty)
                        || !matches!(argument, a::Operand::Move(_))
                    {
                        return Err(unsupported("chunk into_iter signature/type"));
                    }
                    Ok(Some(S::ChunkMove {
                        target: destination,
                        source: self.local(local(operand_place(argument)?)?)?,
                    }))
                } else {
                    if !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "iterator", "Iterator"],
                    ) || !self
                        .adapter
                        .chunk_adt(&imp.impl_trait.generics.types[0], true)
                        || tr.item_meta.lang_item != Some(LangItem::Iterator)
                        || !matches!(callee.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.adapter.chunk_adt(p, true)))
                        || !self.adapter.option_adt(&callee.signature.output, true)
                        || self.adapter.ty(&ptr.generics.types[0])? != Type::U8
                        || self.adapter.chunk_reference(argument.ty()) != Some(true)
                        || !self.adapter.chunk_option_type(&call.dest.ty)
                    {
                        return Err(unsupported("chunk next signature/type"));
                    }
                    Ok(Some(S::ChunkNext {
                        iterator: self.iterator_root(operand_place(argument)?)?,
                        option: destination,
                    }))
                }
            }
            _ => Err(unsupported("unmodeled chunk iterator method")),
        }
    }
}
