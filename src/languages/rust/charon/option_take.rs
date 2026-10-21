//! `Option::take`, rewritten to the move it means.
//!
//! The library defines `o.take()` as `mem::replace(&mut o, None)`. The
//! compiler borrows the option, `r = &mut o`, and calls `take(r)`; when that
//! borrow serves only the call, `t = take(r)` is `t = o; o = None`, for an
//! option of a box as for an option of a scalar.
use super::*;

impl Adapter<'_> {
    /// Whether `call` calls the library's own `Option::take`, at its
    /// declared signature.
    fn option_take_call(&self, call: &a::Call) -> Result<bool, String> {
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(false);
        };
        let a::FnPtrKind::Fun(id) = ptr.kind.as_ref() else {
            return Ok(false);
        };
        let Some(callee) = self.krate.fun_decls.get(*id) else {
            return Ok(false);
        };
        let name = &callee.item_meta.name.name;
        let [
            a::PathElem::Ident(core, d0),
            a::PathElem::Ident(option, d1),
            a::PathElem::Impl(a::ImplElem::Ty(implemented)),
            a::PathElem::Ident(method, d2),
        ] = name.as_slice()
        else {
            return Ok(false);
        };
        if core != "core" || option != "option" || method != "take" {
            return Ok(false);
        }
        let parameter = |ty: &a::Ty| {
            matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id))
                if depth.index == 0 && id.index() == 0)
        };
        let option_of_parameter = |ty: &a::Ty| {
            matches!(ty.kind(), a::TyKind::Adt(r) if r.builtin.is_none()
                && self.krate.type_decls.get(r.id).is_some_and(|decl| {
                    !decl.item_meta.is_local && decl.item_meta.lang_item == Some(LangItem::Option)
                })
                && matches!(r.generics.types.as_raw_slice(), [p] if parameter(p)))
        };
        if !d0.is_zero()
            || !d1.is_zero()
            || !d2.is_zero()
            || callee.item_meta.is_local
            || callee.signature.is_unsafe
            || !matches!(callee.src, a::FunSource::Normal)
            || !option_of_parameter(&implemented.skip_binder)
            || callee.generics.types.len() != 1
            || !callee.generics.const_generics.is_empty()
            || !ptr.generics.const_generics.is_empty()
            || !matches!(callee.signature.inputs.as_slice(), [input]
                if matches!(input.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Mut)
                    if option_of_parameter(pointee)))
            || !option_of_parameter(&callee.signature.output)
            || call.args.len() != 1
        {
            return Err(unsupported("`Option::take` identity"));
        }
        Ok(true)
    }

    /// `body` with each `take` of a borrowed option rewritten to its move,
    /// or `None` when it has none.
    pub(super) fn option_take_body(
        &self,
        body: &u::ExprBody,
    ) -> Result<Option<u::ExprBody>, String> {
        let mut body_copy = None;
        for index in 0..body.body.len() {
            let current = body_copy.as_ref().unwrap_or(body);
            let block = &current.body[u::BlockId::from_usize(index)];
            let u::TerminatorKind::Call { call, target, .. } = &block.terminator.kind else {
                continue;
            };
            if !self.option_take_call(call)? {
                continue;
            }
            let [a::Operand::Move(reference)] = call.args.as_slice() else {
                return Err(unsupported("`Option::take` operand"));
            };
            let Some(reference) = reference.as_local() else {
                return Err(unsupported("`Option::take` operand"));
            };
            // The borrow the call takes, `reference = &mut option`, in the
            // call's own block.
            let Some((borrow, option)) =
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
                return Err(unsupported(
                    "`Option::take` of an option it does not borrow here",
                ));
            };
            let boxed = self.option_box_payload(&option.ty).is_some();
            if !boxed && self.option_payload(&option.ty).is_none() {
                return Err(unsupported("`Option::take` of this option type"));
            }
            let a::TyKind::Adt(option_type) = option.ty.kind().clone() else {
                unreachable!("an option is an ADT")
            };
            // The borrow serves the call alone: no other statement or
            // terminator mentions it.
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
                        return Err(unsupported("`Option::take` borrow used elsewhere"));
                    }
                }
                if other_index != index
                    && mentions(&|visit| other.terminator.dyn_visit(|l: &a::LocalId| visit(l)))
                {
                    return Err(unsupported("`Option::take` borrow used elsewhere"));
                }
            }
            let mut rewritten = current.clone();
            rewritten.locals.locals[reference].ty = a::Ty::mk_unit();
            let block = &mut rewritten.body[u::BlockId::from_usize(index)];
            let span = block.terminator.span;
            let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
                unreachable!()
            };
            let destination = call.dest.clone();
            block.statements = std::mem::take(&mut block.statements)
                .into_iter()
                .enumerate()
                .filter(|(position, statement)| {
                    *position != borrow
                        && !matches!(statement.kind,
                            u::StatementKind::StorageLive(l) | u::StatementKind::StorageDead(l)
                                if l == reference)
                })
                .map(|(_, statement)| statement)
                .collect();
            let source = if boxed {
                a::Operand::Move(option.clone())
            } else {
                a::Operand::Copy(option.clone())
            };
            block.statements.push(u::Statement::new(
                span,
                u::StatementKind::Assign(destination, a::Rvalue::Use(source, a::WithRetag::No)),
            ));
            block.statements.push(u::Statement::new(
                span,
                u::StatementKind::Assign(
                    option,
                    a::Rvalue::Aggregate(
                        a::AggregateKind::Adt(
                            option_type.clone(),
                            Some(a::VariantId::from_usize(0)),
                            None,
                        ),
                        Vec::new(),
                    ),
                ),
            ));
            block.terminator.kind = u::TerminatorKind::Goto { target: *target };
            // Storage statements of the borrow elsewhere go too.
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
