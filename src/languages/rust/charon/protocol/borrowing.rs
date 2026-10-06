use super::*;

// Standard blanket implementations forward reference values without moving the
// iterator state. Resolve these separately from owned iterator moves.
pub(in crate::languages::rust::charon) enum BorrowedProtocolCall {
    Into {
        target: a::LocalId,
        source: a::LocalId,
    },
    Next {
        source: a::LocalId,
        option: a::LocalId,
        shared: bool,
    },
}
impl Adapter<'_> {
    pub(in crate::languages::rust::charon) fn borrowed_protocol_call(
        &self,
        term: &u::Terminator,
    ) -> Result<Option<BorrowedProtocolCall>, String> {
        let u::TerminatorKind::Call { call, .. } = &term.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let callee = self
            .krate
            .fun_decls
            .get(self.resolve(ptr)?)
            .ok_or_else(|| unsupported("missing iterator forwarding declaration"))?;
        let method = match callee.item_meta.name.name.last() {
            Some(a::PathElem::Ident(name, d)) if *d == a::Disambiguator::ZERO => name.as_str(),
            _ => return Ok(None),
        };
        let into = method == "into_iter" && self.protocol_reference(&call.dest.ty) == Some(true);
        let next = method == "next"
            && matches!(ptr.generics.types.iter().next(), Some(ty) if self.protocol_type(ty))
            // An adapter such as Rev<I> also has I as its first type argument.
            // Only the nested mutable receiver belongs to reference forwarding.
            && matches!(call.args.as_slice(), [argument]
                if matches!(argument.ty().kind(), a::TyKind::Ref(_, pointee, a::RefKind::Mut)
                    if matches!(pointee.kind(), a::TyKind::Ref(_, iterator, a::RefKind::Mut)
                        if self.protocol_type(iterator))));
        if !into && !next {
            return Ok(None);
        }
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Err(unsupported("iterator forwarding trait source"));
        };
        let tr = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing iterator forwarding trait"))?;
        let imp = self
            .krate
            .trait_impls
            .get(impl_ref.id)
            .ok_or_else(|| unsupported("missing iterator forwarding implementation"))?;
        let expected = if into { "IntoIterator" } else { "Iterator" };
        let namespace: &[&str] = if into {
            &["core", "iter", "traits", "collect"]
        } else {
            &["core", "iter", "traits", "iterator"]
        };
        if callee.item_meta.is_local || tr.item_meta.is_local || imp.item_meta.is_local
            || callee.signature.is_unsafe || callee.signature.is_variadic || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe || imp.is_unsafe || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || callee.generics.types.len() != 1 || imp.generics.types.len() != 1
            || ptr.generics.types.len() != 1 || !ptr.generics.const_generics.is_empty()
            || !callee.generics.const_generics.is_empty() || !imp.generics.const_generics.is_empty()
            || tr.item_meta.diagnostic_item.as_deref() != Some(expected)
            || !path(&tr.item_meta.name, &[namespace[0], namespace[1], namespace[2], namespace[3], expected])
            || callee.item_meta.name.name.len() != namespace.len() + 2
            || !callee.item_meta.name.name[..namespace.len()].iter().zip(namespace).all(|(p, expected)| matches!(p, a::PathElem::Ident(name, d) if name == expected && *d == a::Disambiguator::ZERO))
            || callee.item_meta.name.name[..callee.item_meta.name.name.len()-1] != imp.item_meta.name.name
            || imp.impl_trait.id != tr.def_id || imp.impl_trait.generics.types.len() != 1
            || !imp.impl_trait.generics.const_generics.is_empty() || item_id.index() != 0
            || tr.methods.get(*item_id).is_none_or(|m| m.skip_binder.name.0 != method)
            || imp.methods.get(*item_id).is_none_or(|m| m.skip_binder.id != callee.def_id)
        { return Err(unsupported("iterator forwarding declaration/identity")) }
        let [argument] = call.args.as_slice() else {
            return Err(unsupported("iterator forwarding arity"));
        };
        if into {
            if !variable(&imp.impl_trait.generics.types[0])
                || !variable(&callee.signature.output)
                || !matches!(callee.signature.inputs.as_slice(), [input] if variable(input))
                || !matches!(argument, a::Operand::Move(_))
                || self.protocol_reference(argument.ty()) != Some(true)
                || self.ty(argument.ty())? != self.ty(&call.dest.ty)?
                || self.ty(&ptr.generics.types[0])? != self.ty(&call.dest.ty)?
            {
                return Err(unsupported("iterator reference into_iter signature/type"));
            }
            return Ok(Some(BorrowedProtocolCall::Into {
                target: local(&call.dest)?,
                source: local(operand_place(argument)?)?,
            }));
        }
        let mutable_variable =
            |ty: &a::Ty| matches!(ty.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if variable(p));
        let signature = matches!(callee.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if mutable_variable(p)));
        let result = match callee.signature.output.kind() {
            a::TyKind::Adt(r)
                if self.krate.type_decls.get(r.id).is_some_and(|t| {
                    !t.item_meta.is_local
                        && t.item_meta.lang_item == Some(LangItem::Option)
                        && path(&t.item_meta.name, &["core", "option", "Option"])
                }) && r.generics.types.len() == 1
                    && r.generics.const_generics.is_empty() =>
            {
                matches!(r.generics.types[0].kind(), a::TyKind::TraitType(t, id, args)
                    if t.trait_id() == tr.def_id && id.index() == 0
                    && matches!(&t.kind, a::TraitRefKind::Clause(a::DeBruijnVar::Bound(depth, clause)) if depth.index == 0 && callee.generics.trait_clauses.get(*clause).is_some_and(|bound| bound.trait_.skip_binder.id == tr.def_id))
                    && t.trait_decl_ref.skip_binder.generics.types.len() == 1
                    // PolyTraitDeclRef introduces its own binder, even without regions.
                    && matches!(t.trait_decl_ref.skip_binder.generics.types[0].kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, variable)) if depth.index == 1 && variable.index() == 0)
                    && args.types.is_empty() && args.const_generics.is_empty() && args.trait_refs.is_empty())
            }
            _ => false,
        };
        let concrete = &ptr.generics.types[0];
        let receiver = matches!(argument.ty().kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if matches!(p.kind(), a::TyKind::Ref(_, i, a::RefKind::Mut) if self.ty(i).ok() == self.ty(concrete).ok()));
        // The resolved bound must select the concrete standard iterator impl,
        // rather than merely having an identically named method.
        let witness = ptr.generics.trait_refs.iter().any(|bound| {
            if bound.trait_id() != tr.def_id || bound.trait_decl_ref.skip_binder.generics.types.len() != 1 || self.ty(&bound.trait_decl_ref.skip_binder.generics.types[0]).ok() != self.ty(concrete).ok() { return false }
            let a::TraitRefKind::TraitImpl(reference) = &bound.kind else { return false };
            let Some(actual) = self.krate.trait_impls.get(reference.id) else { return false };
            if actual.item_meta.is_local || actual.is_unsafe || actual.is_negative || actual.impl_trait.id != tr.def_id { return false }
            let Some(definition) = actual.methods.get(*item_id).and_then(|m| self.krate.fun_decls.get(m.skip_binder.id)) else { return false };
            !definition.item_meta.is_local && !definition.signature.is_unsafe && definition.signature.abi == a::Abi::Rust
                && matches!(definition.signature.inputs.as_slice(), [input] if matches!(input.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.chunk_adt(p, true) || self.shared_iterator_element(p, true).is_some()))
        });
        let matching_option = if self.chunk_type(concrete) {
            self.chunk_option_type(&call.dest.ty)
        } else {
            self.shared_iterator_element(concrete, false)
                .zip(self.shared_option_element(&call.dest.ty, false))
                .is_some_and(|(source, result)| self.ty(source).ok() == self.ty(result).ok())
        };
        for (valid, reason) in [
            (
                tr.item_meta.lang_item == Some(LangItem::Iterator),
                "iterator reference next trait",
            ),
            (
                mutable_variable(&imp.impl_trait.generics.types[0]),
                "iterator reference next implementation receiver",
            ),
            (signature, "iterator reference next input signature"),
            (result, "iterator reference next associated item"),
            (receiver, "iterator reference next argument type"),
            (witness, "iterator reference next resolved bound"),
            (matching_option, "iterator reference next result type"),
        ] {
            if !valid {
                return Err(unsupported(reason));
            }
        }
        Ok(Some(BorrowedProtocolCall::Next {
            source: local(operand_place(argument)?)?,
            option: local(&call.dest)?,
            shared: self.shared_option_element(&call.dest.ty, false).is_some(),
        }))
    }
}
