//! `slice.iter().enumerate()`: the shared slice iterator's state plus the
//! count of values it has yielded. The compiler-resolved `enumerate`,
//! `into_iter` and `next` are checked by identity, and the `(index, &x)`
//! the yielded `Option` holds is read as its two components.
use super::protocol::{local, operand_place, path, variable};
use super::*;

impl Adapter<'_> {
    /// The element of an `Enumerate<Iter<'_, T>>` over a slice of integers.
    pub(super) fn enumerate_element<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        if decl.item_meta.is_local
            || !path(
                &decl.item_meta.name,
                &["core", "iter", "adapters", "enumerate", "Enumerate"],
            )
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
        self.shared_iterator_element(&r.generics.types[0], false)
    }

    /// Whether `ty` is an `Enumerate` instance, at a type parameter with
    /// `template`.
    fn enumerate_template(&self, ty: &a::Ty) -> bool {
        matches!(ty.kind(), a::TyKind::Adt(r)
            if self.krate.type_decls.get(r.id).is_some_and(|decl| path(
                &decl.item_meta.name,
                &["core", "iter", "adapters", "enumerate", "Enumerate"],
            ))
            && matches!(r.generics.types.as_raw_slice(), [inner] if variable(inner)))
    }

    /// The element of the `Option<(usize, &T)>` an enumerated slice
    /// iterator yields.
    pub(super) fn enumerate_option_element<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [payload] = r.generics.types.as_raw_slice() else {
            return None;
        };
        if decl.item_meta.is_local
            || decl.item_meta.lang_item != Some(LangItem::Option)
            || !path(&decl.item_meta.name, &["core", "option", "Option"])
        {
            return None;
        }
        let a::TyKind::Adt(tuple) = payload.kind() else {
            return None;
        };
        let [index, reference] = tuple.generics.types.as_raw_slice() else {
            return None;
        };
        if tuple.builtin != Some(a::BuiltinAdt::Tuple)
            || !matches!(
                index.kind(),
                a::TyKind::Scalar(a::ScalarTy::Integer(a::IntegerTy::Unsigned(
                    a::UIntTy::Usize
                )))
            )
        {
            return None;
        }
        let a::TyKind::Ref(_, element, a::RefKind::Shared) = reference.kind() else {
            return None;
        };
        self.ty(element)
            .is_ok_and(|element| element.is_integer())
            .then_some(element)
    }
}

impl BodyAdapter<'_, '_> {
    /// An enumerated iterator's `enumerate`, `into_iter` or `next`.
    pub(super) fn enumerate_call(&self, t: &u::Terminator) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &t.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let made = self.adapter.enumerate_element(&call.dest.ty);
        let advanced = self.adapter.enumerate_option_element(&call.dest.ty);
        if made.is_none() && advanced.is_none() {
            return Ok(None);
        }
        let callee = self
            .adapter
            .krate
            .fun_decls
            .get(self.adapter.resolve(ptr)?)
            .ok_or_else(|| unsupported("missing enumerate method declaration"))?;
        let method = match callee.item_meta.name.name.last() {
            Some(a::PathElem::Ident(method, d)) if *d == a::Disambiguator::ZERO => method.as_str(),
            _ => return Err(unsupported("enumerate method identity")),
        };
        let [argument] = call.args.as_slice() else {
            return Err(unsupported("enumerate method arity"));
        };
        if callee.item_meta.is_local
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
        {
            return Err(unsupported("enumerate method declaration"));
        }
        let destination = self.local(local(&call.dest)?)?;
        let element = |ty: Option<&a::Ty>| ty.map(|ty| self.adapter.ty(ty)).transpose();
        match &callee.src {
            // `Iterator::enumerate`, the trait's own default method.
            a::FunSource::TraitDefault { trait_ref, item_id } => {
                let tr = &self.adapter.krate.trait_decls[trait_ref.id];
                if method != "enumerate"
                    || !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "iterator", "Iterator"],
                    )
                    || tr.item_meta.lang_item != Some(LangItem::Iterator)
                    || tr.item_meta.is_local
                    || tr
                        .methods
                        .get(*item_id)
                        .is_none_or(|m| m.skip_binder.name.0 != method)
                    || ptr.generics.types.len() != 1
                    || !matches!(argument, a::Operand::Move(_))
                    || element(self.adapter.shared_iterator_element(argument.ty(), false))?
                        .is_none()
                    || element(self.adapter.shared_iterator_element(argument.ty(), false))?
                        != element(made)?
                {
                    return Err(unsupported("enumerate identity/signature"));
                }
                Ok(Some(S::EnumerateInitialize {
                    target: destination,
                    source: self.local(local(operand_place(argument)?)?)?,
                }))
            }
            a::FunSource::TraitImpl {
                trait_ref,
                impl_ref,
                item_id,
                ..
            } => {
                let tr = &self.adapter.krate.trait_decls[trait_ref.id];
                let imp = &self.adapter.krate.trait_impls[impl_ref.id];
                if tr.item_meta.is_local
                    || imp.item_meta.is_local
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
                    return Err(unsupported("enumerate trait/implementation identity"));
                }
                let receiver = imp
                    .impl_trait
                    .generics
                    .types
                    .iter()
                    .next()
                    .ok_or_else(|| unsupported("enumerate receiver"))?;
                if made.is_some() {
                    // The standard `impl<I: Iterator> IntoIterator for I`.
                    if method != "into_iter"
                        || !path(
                            &tr.item_meta.name,
                            &["core", "iter", "traits", "collect", "IntoIterator"],
                        )
                        || tr.item_meta.diagnostic_item.as_deref() != Some("IntoIterator")
                        || !variable(receiver)
                        || !matches!(argument, a::Operand::Move(_))
                        || self.adapter.ty(argument.ty())? != self.adapter.ty(&call.dest.ty)?
                    {
                        return Err(unsupported("enumerate into_iter identity/signature"));
                    }
                    return Ok(Some(S::EnumerateMove {
                        target: destination,
                        source: self.local(local(operand_place(argument)?)?)?,
                    }));
                }
                // The standard `impl<I: Iterator> Iterator for Enumerate<I>`.
                let a::TyKind::Ref(_, iterator, a::RefKind::Mut) = argument.ty().kind() else {
                    return Err(unsupported("enumerate next receiver"));
                };
                if method != "next"
                    || !path(
                        &tr.item_meta.name,
                        &["core", "iter", "traits", "iterator", "Iterator"],
                    )
                    || tr.item_meta.lang_item != Some(LangItem::Iterator)
                    || !self.adapter.enumerate_template(receiver)
                    || element(self.adapter.enumerate_element(iterator))? != element(advanced)?
                {
                    return Err(unsupported("enumerate next identity/signature"));
                }
                Ok(Some(S::EnumerateNext {
                    iterator: self.iterator_root(operand_place(argument)?)?,
                    option: destination,
                }))
            }
            _ => Err(unsupported("enumerate method source")),
        }
    }

    /// The index or the element address an enumerated iterator's `Some`
    /// holds: `(option as Some).0.0` or `.0.1`.
    pub(super) fn enumerate_projection(&self, place: &a::Place) -> Result<Option<E>, String> {
        let a::PlaceKind::Projection(tuple, a::ProjectionElem::Field(None, component)) =
            &place.kind
        else {
            return Ok(None);
        };
        let a::PlaceKind::Projection(option, a::ProjectionElem::Field(Some(variant), field)) =
            &tuple.kind
        else {
            return Ok(None);
        };
        if self.adapter.enumerate_option_element(&option.ty).is_none() {
            return Ok(None);
        }
        if variant.index() != 1 || field.index() != 0 {
            return Err(unsupported("enumerate Option projection"));
        }
        let option = self.local(local(option)?)?;
        match component.index() {
            0 => Ok(Some(E::EnumerateOptionIndex { option })),
            1 => Ok(Some(E::SharedArrayOptionElement { option })),
            _ => Err(unsupported("enumerate Option component")),
        }
    }
}
