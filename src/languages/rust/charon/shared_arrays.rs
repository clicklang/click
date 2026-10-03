//! Named shared scalar iteration. Compiler-selected declarations, signatures,
//! trait implementations and concrete element instantiations are all checked.
use super::protocol::{local, operand_place, path, variable};
use super::*;

fn scalar(adapter: &Adapter<'_>, ty: &a::Ty, template: bool) -> bool {
    if template {
        variable(ty)
    } else {
        matches!(adapter.ty(ty), Ok(Type::I32 | Type::U8 | Type::U32))
    }
}
impl Adapter<'_> {
    pub(super) fn shared_iterator_element<'t>(
        &self,
        ty: &'t a::Ty,
        template: bool,
    ) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        if decl.item_meta.is_local
            || !path(&decl.item_meta.name, &["core", "slice", "iter", "Iter"])
            || !matches!(decl.src, a::TypeSource::Normal)
            || !matches!(decl.kind, a::TypeDeclKind::Opaque)
            || decl.generics.regions.len() != 1
            || r.generics.regions.len() != 1
            || decl.generics.types.len() != 1
            || r.generics.types.len() != 1
            || !decl.generics.const_generics.is_empty()
            || !r.generics.const_generics.is_empty()
        {
            return None;
        }
        scalar(self, &r.generics.types[0], template).then_some(&r.generics.types[0])
    }
    pub(super) fn shared_option_element<'t>(
        &self,
        ty: &'t a::Ty,
        template: bool,
    ) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        if decl.item_meta.is_local
            || decl.item_meta.lang_item != Some(LangItem::Option)
            || !path(&decl.item_meta.name, &["core", "option", "Option"])
            || !matches!(decl.src, a::TypeSource::Normal)
            || !matches!(decl.kind, a::TypeDeclKind::Opaque)
            || !decl.generics.regions.is_empty()
            || !r.generics.regions.is_empty()
            || decl.generics.types.len() != 1
            || r.generics.types.len() != 1
            || !decl.generics.const_generics.is_empty()
            || !r.generics.const_generics.is_empty()
        {
            return None;
        }
        let a::TyKind::Ref(_, element, a::RefKind::Shared) = r.generics.types[0].kind() else {
            return None;
        };
        scalar(self, element, template).then_some(element)
    }
}
impl BodyAdapter<'_, '_> {
    pub(super) fn shared_array_call(
        &self,
        terminator: &u::Terminator,
    ) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &terminator.kind else {
            return Ok(None);
        };
        let relevant = self
            .adapter
            .shared_iterator_element(&call.dest.ty, false)
            .is_some()
            || self
                .adapter
                .shared_option_element(&call.dest.ty, false)
                .is_some();
        if !relevant {
            return Ok(None);
        }
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Err(unsupported("shared iterator callee"));
        };
        let callee = &self.adapter.krate.fun_decls[self.adapter.resolve(ptr)?];
        if callee.item_meta.is_local
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || callee.generics.types.len() != 1
            || ptr.generics.types.len() != 1
        {
            return Err(unsupported("shared iterator declaration/type mismatch"));
        }
        let name = &callee.item_meta.name.name;
        let Some(a::PathElem::Ident(method, d)) = name.last() else {
            return Err(unsupported("shared iterator method identity"));
        };
        if *d != a::Disambiguator::ZERO {
            return Err(unsupported("shared iterator method disambiguator"));
        }
        let destination = self.local(local(&call.dest)?)?;
        let [argument] = call.args.as_slice() else {
            return Err(unsupported("shared iterator arity"));
        };
        let element = self.adapter.ty(&ptr.generics.types[0])?;
        if let a::FunSource::Normal = callee.src {
            if method != "iter"
                || name.len() != 4
                || !matches!(&name[0..2], [a::PathElem::Ident(core, d0), a::PathElem::Ident(slice, d1)] if core == "core" && slice == "slice" && *d0 == a::Disambiguator::ZERO && *d1 == a::Disambiguator::ZERO)
                || !callee.generics.const_generics.is_empty()
                || !ptr.generics.const_generics.is_empty()
            {
                return Err(unsupported("shared slice iter identity"));
            }
            let a::PathElem::Impl(a::ImplElem::Ty(receiver)) = &name[2] else {
                return Err(unsupported("shared slice iter receiver"));
            };
            if !matches!(receiver.skip_binder.kind(), a::TyKind::Slice(e, _) if variable(e))
                || !matches!(callee.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if matches!(p.kind(), a::TyKind::Slice(e, _) if variable(e))))
                || self
                    .adapter
                    .shared_iterator_element(&callee.signature.output, true)
                    .is_none()
                || self
                    .adapter
                    .shared_iterator_element(&call.dest.ty, false)
                    .is_none_or(|e| self.adapter.ty(e).ok() != Some(element.clone()))
                || !matches!(argument.ty().kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if matches!(p.kind(), a::TyKind::Slice(e, _) if self.adapter.ty(e).ok() == Some(element.clone())))
            {
                return Err(unsupported("shared slice iter signature/element"));
            }
            return Ok(Some(S::SharedArrayInitialize {
                target: destination,
                source: self.operand(argument)?,
            }));
        }
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Err(unsupported("shared iterator trait source"));
        };
        let tr = &self.adapter.krate.trait_decls[trait_ref.id];
        let imp = &self.adapter.krate.trait_impls[impl_ref.id];
        if tr.item_meta.is_local
            || imp.item_meta.is_local
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || name[..name.len() - 1] != imp.item_meta.name.name
            || imp.impl_trait.generics.types.len() != 1
            || !imp.impl_trait.generics.const_generics.is_empty()
            || item_id.index() != 0
            || tr
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.name.0 != *method)
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.id != callee.def_id)
        {
            return Err(unsupported("shared iterator trait/implementation identity"));
        }
        let implementation_path = &imp.item_meta.name.name;
        let expected_prefix: &[&str] = if method == "next" {
            &["core", "slice", "iter"]
        } else if variable(&imp.impl_trait.generics.types[0]) {
            &["core", "iter", "traits", "collect"]
        } else {
            &["core", "array"]
        };
        if implementation_path.len() != expected_prefix.len() + 1
            || !implementation_path[..expected_prefix.len()].iter().zip(expected_prefix).all(|(part, expected)| matches!(part, a::PathElem::Ident(actual, d) if actual == expected && *d == a::Disambiguator::ZERO))
            || !matches!(implementation_path.last(), Some(a::PathElem::Impl(a::ImplElem::Trait(id))) if *id == impl_ref.id)
        { return Err(unsupported("shared iterator implementation path")); }
        let receiver = &imp.impl_trait.generics.types[0];
        match method.as_str() {
            "next" => {
                if !path(
                    &tr.item_meta.name,
                    &["core", "iter", "traits", "iterator", "Iterator"],
                ) || tr.item_meta.lang_item != Some(LangItem::Iterator)
                    || tr.item_meta.diagnostic_item.as_deref() != Some("Iterator")
                    || self
                        .adapter
                        .shared_iterator_element(receiver, true)
                        .is_none()
                    || !callee.generics.const_generics.is_empty()
                    || !ptr.generics.const_generics.is_empty()
                    || !matches!(callee.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.adapter.shared_iterator_element(p, true).is_some()))
                    || self
                        .adapter
                        .shared_option_element(&callee.signature.output, true)
                        .is_none()
                    || self
                        .adapter
                        .shared_option_element(&call.dest.ty, false)
                        .is_none_or(|e| self.adapter.ty(e).ok() != Some(element.clone()))
                    || !matches!(argument.ty().kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.adapter.shared_iterator_element(p, false).is_some_and(|e| self.adapter.ty(e).ok() == Some(element.clone())))
                {
                    return Err(unsupported("shared iterator next signature/element"));
                }
                Ok(Some(S::SharedArrayNext {
                    iterator: self.iterator_root(operand_place(argument)?)?,
                    option: destination,
                }))
            }
            "into_iter" => {
                if !path(
                    &tr.item_meta.name,
                    &["core", "iter", "traits", "collect", "IntoIterator"],
                ) || tr.item_meta.diagnostic_item.as_deref() != Some("IntoIterator")
                {
                    return Err(unsupported("shared iterator into_iter trait identity"));
                }
                if variable(receiver) {
                    if !variable(&callee.signature.output)
                        || !matches!(callee.signature.inputs.as_slice(), [input] if variable(input))
                        || !callee.generics.const_generics.is_empty()
                        || !ptr.generics.const_generics.is_empty()
                        || !matches!(argument, a::Operand::Move(_))
                        || self.adapter.ty(argument.ty())? != self.adapter.ty(&call.dest.ty)?
                        || self
                            .adapter
                            .shared_iterator_element(argument.ty(), false)
                            .is_none()
                    {
                        return Err(unsupported("shared iterator into_iter move signature"));
                    }
                    Ok(Some(S::SharedArrayMove {
                        target: destination,
                        source: self.local(local(operand_place(argument)?)?)?,
                    }))
                } else {
                    if !matches!(receiver.kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if matches!(p.kind(), a::TyKind::Array(e, n, _) if variable(e) && matches!(n.kind(), a::ConstantExprKind::Var(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 && id.index() == 0)))
                        || !matches!(callee.signature.inputs.as_slice(), [input] if input == receiver)
                        || self
                            .adapter
                            .shared_iterator_element(&callee.signature.output, true)
                            .is_none()
                        || callee.generics.const_generics.len() != 1
                        || ptr.generics.const_generics.len() != 1
                        || self
                            .adapter
                            .shared_iterator_element(&call.dest.ty, false)
                            .is_none_or(|e| self.adapter.ty(e).ok() != Some(element.clone()))
                        || !matches!(argument.ty().kind(), a::TyKind::Ref(_, p, a::RefKind::Shared) if matches!(p.kind(), a::TyKind::Array(e, n, _) if self.adapter.ty(e).ok() == Some(element.clone()) && n.as_usize_literal() == ptr.generics.const_generics[0].as_usize_literal() && n.as_usize_literal().is_some()))
                    {
                        return Err(unsupported("shared array into_iter signature/extent"));
                    }
                    Ok(Some(S::SharedArrayInitialize {
                        target: destination,
                        source: self.operand(argument)?,
                    }))
                }
            }
            _ => Err(unsupported("unmodeled shared array iterator method")),
        }
    }
}
