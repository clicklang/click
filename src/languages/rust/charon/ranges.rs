//! Integer ranges, `start..end`, iterated by `for`. The compiler-resolved
//! `IntoIterator::into_iter` and `Iterator::next` of `core::ops::Range` are
//! checked by identity and lowered to the range's two bounds; `next` yields
//! an ordinary `Option` value.
use super::protocol::{local, operand_place, path, variable};
use super::*;

impl Adapter<'_> {
    /// The element of a `core::ops::Range<T>` of an integer `T`, or with
    /// `template` of the declaration's own type parameter.
    pub(super) fn range_element<'t>(&self, ty: &'t a::Ty, template: bool) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        if decl.item_meta.is_local
            || !path(&decl.item_meta.name, &["core", "ops", "range", "Range"])
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
        let element = &r.generics.types[0];
        let admitted = if template {
            variable(element)
        } else {
            self.ty(element).is_ok_and(|element| element.is_integer())
        };
        admitted.then_some(element)
    }
}

impl BodyAdapter<'_, '_> {
    /// A range local's construction, `start..end`, or its move.
    pub(super) fn range_statement(&self, s: &u::Statement) -> Result<Option<S>, String> {
        let u::StatementKind::Assign(target, value) = &s.kind else {
            return Ok(None);
        };
        let Some(element) = self.adapter.range_element(&target.ty, false) else {
            return Ok(None);
        };
        let element = self.adapter.ty(element)?;
        let target_name = self.local(local(target)?)?;
        match value {
            a::Rvalue::Aggregate(a::AggregateKind::Adt(r, None, None), fields) if matches!(target.ty.kind(), a::TyKind::Adt(t) if t.id == r.id) =>
            {
                let [start, end] = fields.as_slice() else {
                    return Err(unsupported("range aggregate arity"));
                };
                if self.adapter.ty(start.ty())? != element || self.adapter.ty(end.ty())? != element
                {
                    return Err(unsupported("range bound type"));
                }
                Ok(Some(S::RangeInitialize {
                    target: target_name,
                    start: self.operand(start)?,
                    end: self.operand(end)?,
                }))
            }
            a::Rvalue::Use(a::Operand::Move(source), _)
                if self.adapter.ty(&source.ty)? == self.adapter.ty(&target.ty)? =>
            {
                Ok(Some(S::RangeMove {
                    target: target_name,
                    source: self.local(local(source)?)?,
                }))
            }
            _ => Err(unsupported("range value other than `start..end` or a move")),
        }
    }

    /// A range's `into_iter`, which returns the range itself, or its `next`.
    pub(super) fn range_call(&self, t: &u::Terminator) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &t.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let into = self.adapter.range_element(&call.dest.ty, false).is_some();
        let next = matches!(call.args.as_slice(), [argument]
            if matches!(argument.ty().kind(), a::TyKind::Ref(_, range, a::RefKind::Mut)
                if self.adapter.range_element(range, false).is_some()));
        if !into && !next {
            return Ok(None);
        }
        let callee = self
            .adapter
            .krate
            .fun_decls
            .get(self.adapter.resolve(ptr)?)
            .ok_or_else(|| unsupported("missing range method declaration"))?;
        let method = match callee.item_meta.name.name.last() {
            Some(a::PathElem::Ident(method, d)) if *d == a::Disambiguator::ZERO => method.as_str(),
            _ => return Err(unsupported("range method identity")),
        };
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Err(unsupported("range method other than `into_iter` or `next`"));
        };
        let tr = &self.adapter.krate.trait_decls[trait_ref.id];
        let imp = &self.adapter.krate.trait_impls[impl_ref.id];
        let [argument] = call.args.as_slice() else {
            return Err(unsupported("range method arity"));
        };
        if callee.item_meta.is_local
            || tr.item_meta.is_local
            || imp.item_meta.is_local
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || tr
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.name.0 != method)
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.id != callee.def_id)
        {
            return Err(unsupported("range iterator trait/implementation identity"));
        }
        let receiver = imp
            .impl_trait
            .generics
            .types
            .iter()
            .next()
            .ok_or_else(|| unsupported("range iterator receiver"))?;
        let destination = self.local(local(&call.dest)?)?;
        if into {
            // The standard `impl<I: Iterator> IntoIterator for I` returns
            // its receiver.
            if method != "into_iter"
                || !path(
                    &tr.item_meta.name,
                    &["core", "iter", "traits", "collect", "IntoIterator"],
                )
                || tr.item_meta.diagnostic_item.as_deref() != Some("IntoIterator")
                || !variable(receiver)
                || !variable(&callee.signature.output)
                || !matches!(callee.signature.inputs.as_slice(), [input] if variable(input))
                || !matches!(argument, a::Operand::Move(_))
                || self.adapter.ty(argument.ty())? != self.adapter.ty(&call.dest.ty)?
            {
                return Err(unsupported("range into_iter identity/signature"));
            }
            return Ok(Some(S::RangeMove {
                target: destination,
                source: self.local(local(operand_place(argument)?)?)?,
            }));
        }
        // The standard `impl<A: Step> Iterator for Range<A>`'s `next`.
        let a::TyKind::Ref(_, range, _) = argument.ty().kind() else {
            unreachable!("checked above")
        };
        let element = self.adapter.ty(self
            .adapter
            .range_element(range, false)
            .expect("checked above"))?;
        let payload = self
            .adapter
            .option_payload(&call.dest.ty)
            .map(|payload| self.adapter.ty(payload))
            .transpose()?;
        if method != "next"
            || !path(
                &tr.item_meta.name,
                &["core", "iter", "traits", "iterator", "Iterator"],
            )
            || tr.item_meta.lang_item != Some(LangItem::Iterator)
            || self.adapter.range_element(receiver, true).is_none()
            || payload != Some(element)
        {
            return Err(unsupported("range next identity/signature"));
        }
        let Type::Enum { name: option_type } = self.adapter.ty(&call.dest.ty)? else {
            return Err(unsupported("range next Option type"));
        };
        Ok(Some(S::RangeNext {
            iterator: self.iterator_root(operand_place(argument)?)?,
            option: destination,
            option_type,
        }))
    }
}
