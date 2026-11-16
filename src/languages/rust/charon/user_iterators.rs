//! A crate's own `impl Iterator for S`: its `next` is a function of the crate
//! like any other, imported with its body, `S_next(self: &mut S) ->
//! Option<Item>`. A `for` loop over an `S` calls it as the compiler's
//! desugaring does; nothing about the iterator is modeled.
use super::*;

impl Adapter<'_> {
    /// Whether `tr` is `core::iter::Iterator`.
    pub(super) fn is_core_iterator(tr: &a::TraitDecl) -> bool {
        !tr.item_meta.is_local
            && tr.item_meta.lang_item == Some(LangItem::Iterator)
            && protocol::path(
                &tr.item_meta.name,
                &["core", "iter", "traits", "iterator", "Iterator"],
            )
    }

    /// The name of a crate's `Iterator::next` for its own struct `S`,
    /// `S_next`, after checking that `f` is that method of a local, non-generic
    /// implementation.
    pub(super) fn user_iterator_next_name(&self, f: &a::FunDecl) -> Result<String, String> {
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &f.src
        else {
            return Err(unsupported("iterator method source"));
        };
        let tr = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing Iterator trait"))?;
        let imp = self
            .krate
            .trait_impls
            .get(impl_ref.id)
            .ok_or_else(|| unsupported("missing Iterator implementation"))?;
        let method = tr
            .methods
            .get(*item_id)
            .ok_or_else(|| unsupported("missing Iterator method"))?;
        if !Self::is_core_iterator(tr)
            || method.skip_binder.name.0 != "next"
            || !imp.item_meta.is_local
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || !imp.generics.types.is_empty()
            || !imp.generics.const_generics.is_empty()
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.id != f.def_id)
            || !f.item_meta.is_local
            || !matches!(f.body, a::Body::Unstructured(_))
            || f.signature.is_unsafe
            || f.signature.is_variadic
            || f.signature.abi != a::Abi::Rust
            || !f.generics.types.is_empty()
            || !f.generics.const_generics.is_empty()
            || !local_impl_method_path(
                &f.item_meta.name,
                &self.krate.crate_name,
                impl_ref.id,
                "next",
            )
        {
            return Err(unsupported(
                "Iterator::next declaration/implementation identity",
            ));
        }
        let self_ty = imp
            .impl_trait
            .generics
            .types
            .first()
            .ok_or_else(|| unsupported("Iterator implementation receiver"))?;
        let record = self.record_id(self_ty)?;
        let [receiver] = f.signature.inputs.as_slice() else {
            return Err(unsupported("Iterator::next arity"));
        };
        if !matches!(receiver.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.record_id(p).ok() == Some(record))
        {
            return Err(unsupported("Iterator::next receiver"));
        }
        Ok(format!("{}_next", self.records[&record]))
    }
}

impl BodyAdapter<'_, '_> {
    /// `IntoIterator::into_iter(s)` for a crate struct `S` that implements
    /// `Iterator`: `core`'s `impl<I: Iterator> IntoIterator for I` returns
    /// its argument, so the call is a move of `s`.
    pub(super) fn user_iterator_into_iter(
        &self,
        terminator: &u::Terminator,
    ) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &terminator.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let callee = &self.adapter.krate.fun_decls[self.adapter.resolve(ptr)?];
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            ..
        } = &callee.src
        else {
            return Ok(None);
        };
        let tr = &self.adapter.krate.trait_decls[trait_ref.id];
        if tr.item_meta.is_local
            || tr.item_meta.diagnostic_item.as_deref() != Some("IntoIterator")
            || !protocol::path(
                &tr.item_meta.name,
                &["core", "iter", "traits", "collect", "IntoIterator"],
            )
        {
            return Ok(None);
        }
        let [a::Operand::Move(source)] = call.args.as_slice() else {
            return Ok(None);
        };
        let Ok(record) = self.adapter.record_id(&source.ty) else {
            return Ok(None);
        };
        let imp = &self.adapter.krate.trait_impls[impl_ref.id];
        if imp.item_meta.is_local
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.generics.types.len() != 1
            || !protocol::variable(&imp.impl_trait.generics.types[0])
            || ptr.generics.types.len() != 1
            || self.adapter.record_id(&ptr.generics.types[0]).ok() != Some(record)
            || self.adapter.record_id(&call.dest.ty).ok() != Some(record)
            || !matches!(callee.signature.output.kind(), a::TyKind::TypeVar(_))
        {
            return Err(unsupported("IntoIterator::into_iter of a crate iterator"));
        }
        let (a::PlaceKind::Local(source), a::PlaceKind::Local(destination)) =
            (&source.kind, &call.dest.kind)
        else {
            return Err(unsupported("projected into_iter operand or destination"));
        };
        Ok(Some(S::Move {
            target: self.local(*destination)?,
            source: self.local(*source)?,
            record: self.adapter.records[&record].clone(),
        }))
    }
}

/// Each crate iterator's `next()` whose `Option` its `match` dispatches at
/// once, as a `for` loop's does: the `match` becomes a test of the call's
/// result, `VariantIs { Some }`, so the loop's header is the call and that
/// test. The `Some` arm still reads the payload from the result.
pub(super) fn test_user_next_results(blocks: &mut [out::MirBlock], nexts: &BTreeSet<String>) {
    for index in 0..blocks.len() {
        let T::Call {
            function,
            destination,
            target,
            ..
        } = &blocks[index].terminator
        else {
            continue;
        };
        if !nexts.contains(function) {
            continue;
        }
        let (destination, dispatch) = (destination.clone(), *target);
        let Some(block) = blocks.get(dispatch) else {
            continue;
        };
        let T::Switch {
            scrutinee: E::Local { name },
            cases,
            otherwise: None,
        } = &block.terminator
        else {
            continue;
        };
        if *name != destination
            || !block.statements.iter().all(|statement| {
                matches!(
                    statement,
                    S::Site { .. } | S::BeginStorage { .. } | S::EndStorage { .. }
                )
            })
        {
            continue;
        }
        let target = |variant: &str| {
            cases.iter().find_map(|case| match &case.label {
                out::SwitchLabel::Variant { name } if name == variant => Some(case.target),
                _ => None,
            })
        };
        let (Some(some), Some(none), 2) = (target("Some"), target("None"), cases.len()) else {
            continue;
        };
        blocks[dispatch].terminator = T::If {
            condition: E::VariantIs {
                value: Box::new(E::Local { name: destination }),
                variant: "Some".into(),
            },
            then_target: some,
            else_target: none,
        };
    }
}
