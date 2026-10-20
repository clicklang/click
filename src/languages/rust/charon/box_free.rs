//! The free of a box whose contents were moved out.
//!
//! Moving a field out of a box, `self.head = node.next`, leaves the box
//! partly moved. The compiler then drops the fields still owned in place and
//! frees the allocation by calling `<Box<R> as Drop>::drop(&mut node)`, which
//! the library defines as the deallocation alone. When the borrow serves only
//! the call, the call is `node`'s free without its record's drop glue.
use super::*;

impl Adapter<'_> {
    /// Whether `call` calls the library's own `<Box<T, A> as Drop>::drop`.
    pub(super) fn box_drop_call(&self, call: &a::Call) -> Result<bool, String> {
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(false);
        };
        let Ok(id) = self.resolve(ptr) else {
            return Ok(false);
        };
        let Some(callee) = self.krate.fun_decls.get(id) else {
            return Ok(false);
        };
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            ..
        } = &callee.src
        else {
            return Ok(false);
        };
        let Some(tr) = self.krate.trait_decls.get(trait_ref.id) else {
            return Ok(false);
        };
        let Some(imp) = self.krate.trait_impls.get(impl_ref.id) else {
            return Ok(false);
        };
        let boxed = |ty: &a::Ty| matches!(ty.kind(), a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Box));
        if tr.item_meta.lang_item != Some(LangItem::Drop)
            || !imp.impl_trait.generics.types.first().is_some_and(boxed)
        {
            return Ok(false);
        }
        if tr.item_meta.is_local
            || callee.item_meta.is_local
            || imp.item_meta.is_local
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || !matches!(callee.item_meta.name.name.as_slice(),
                [a::PathElem::Ident(alloc, _), a::PathElem::Ident(module, _), .., a::PathElem::Ident(method, _)]
                    if alloc == "alloc" && module == "boxed" && method == "drop")
            || !matches!(callee.signature.inputs.as_slice(), [input]
                if matches!(input.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Mut) if boxed(pointee)))
            || !callee.signature.output.is_unit()
            || call.args.len() != 1
        {
            return Err(unsupported("`Box` drop identity"));
        }
        Ok(true)
    }

    /// `body` with each `<Box as Drop>::drop(&mut b)` taking `b` itself, its
    /// borrow gone, or `None` when it has none.
    pub(super) fn box_free_body(&self, body: &u::ExprBody) -> Result<Option<u::ExprBody>, String> {
        let mut body_copy = None;
        for index in 0..body.body.len() {
            let current = body_copy.as_ref().unwrap_or(body);
            let block = &current.body[u::BlockId::from_usize(index)];
            let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
                continue;
            };
            if !self.box_drop_call(call)? {
                continue;
            }
            let [a::Operand::Move(reference)] = call.args.as_slice() else {
                return Err(unsupported("`Box` drop operand"));
            };
            let Some(reference) = reference.as_local() else {
                return Err(unsupported("`Box` drop operand"));
            };
            // The borrow the call takes, `reference = &mut b`, in the call's
            // own block.
            let Some((borrow, boxed)) =
                block
                    .statements
                    .iter()
                    .enumerate()
                    .find_map(|(position, statement)| match &statement.kind {
                        u::StatementKind::Assign(
                            target,
                            a::Rvalue::Ref {
                                place,
                                kind: a::BorrowKind::Mut | a::BorrowKind::TwoPhaseMut,
                                ..
                            },
                        ) if target.as_local() == Some(reference) => {
                            Some((position, place.clone()))
                        }
                        _ => None,
                    })
            else {
                return Err(unsupported("`Box` drop of a box it does not borrow here"));
            };
            if boxed.as_local().is_none() || !matches!(self.ty(&boxed.ty), Ok(Type::Box { .. })) {
                return Err(unsupported("`Box` drop of this place"));
            }
            // The borrow serves the call alone.
            let mentions = |item: &dyn Fn(&mut dyn FnMut(&a::LocalId))| {
                let mut found = false;
                item(&mut |local| found |= *local == reference);
                found
            };
            for (other_index, other) in current.body.iter().enumerate() {
                for (position, statement) in other.statements.iter().enumerate() {
                    if (other_index == index && position == borrow)
                        || matches!(statement.kind,
                            u::StatementKind::StorageLive(l) | u::StatementKind::StorageDead(l)
                                if l == reference)
                    {
                        continue;
                    }
                    if mentions(&|visit| statement.dyn_visit(|l: &a::LocalId| visit(l))) {
                        return Err(unsupported("`Box` drop borrow used elsewhere"));
                    }
                }
                if other_index != index
                    && mentions(&|visit| other.terminator.dyn_visit(|l: &a::LocalId| visit(l)))
                {
                    return Err(unsupported("`Box` drop borrow used elsewhere"));
                }
            }
            let mut rewritten = current.clone();
            rewritten.locals.locals[reference].ty = a::Ty::mk_unit();
            let block = &mut rewritten.body[u::BlockId::from_usize(index)];
            block.statements.remove(borrow);
            let u::TerminatorKind::Call { call, .. } = &mut block.terminator.kind else {
                unreachable!()
            };
            call.args = vec![a::Operand::Move(boxed)];
            for other in rewritten.body.iter_mut() {
                other.statements.retain(|statement| {
                    !matches!(statement.kind,
                        u::StatementKind::StorageLive(l) | u::StatementKind::StorageDead(l)
                            if l == reference)
                });
            }
            body_copy = Some(rewritten);
        }
        Ok(body_copy)
    }
}
