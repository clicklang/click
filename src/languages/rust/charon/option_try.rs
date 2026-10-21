//! The `?` operator on an `Option`, rewritten to the `match` it means.
//!
//! `o?` calls `<Option<T> as Try>::branch(o)`, matches the resulting
//! `ControlFlow<Option<!>, T>`, and on `Break(residual)` returns
//! `<Option<U> as FromResidual<Option<!>>>::from_residual(residual)`. The
//! library defines `branch(Some(v))` as `Continue(v)`, `branch(None)` as
//! `Break(None)`, and `from_residual(None)` as `None`, the only value of
//! `Option<!>`. So the `ControlFlow` local is the option itself, its
//! `Continue` field is `Some`'s, and the call on the `Break` edge is `None`.
use super::protocol::path;
use super::*;

/// One of the two library functions a `?` on an `Option` calls.
#[derive(Clone, Copy, PartialEq)]
enum TryCall {
    Branch,
    FromResidual,
}

fn bound_parameter(ty: &a::Ty) -> bool {
    matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id))
        if depth.index == 0 && id.index() == 0)
}

impl Adapter<'_> {
    fn option_declaration(&self, id: a::TypeDeclId) -> bool {
        self.krate.type_decls.get(id).is_some_and(|decl| {
            !decl.item_meta.is_local && decl.item_meta.lang_item == Some(LangItem::Option)
        })
    }
    /// The payload of an `Option<P>` whose payload `payload` accepts.
    fn option_of(&self, ty: &a::Ty, payload: impl Fn(&a::Ty) -> bool) -> bool {
        matches!(ty.kind(), a::TyKind::Adt(r) if r.builtin.is_none()
            && self.option_declaration(r.id)
            && matches!(r.generics.types.as_raw_slice(), [p] if payload(p)))
    }
    /// Whether `ty` is `Option<!>`, the residual of a `?` on an `Option`.
    fn option_residual(&self, ty: &a::Ty) -> bool {
        self.option_of(ty, |p| matches!(p.kind(), a::TyKind::Never))
    }
    /// The `C` of a `core::ops::ControlFlow<Option<!>, C>`.
    fn option_control_flow<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [residual, output] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (r.builtin.is_none()
            && !decl.item_meta.is_local
            && path(
                &decl.item_meta.name,
                &["core", "ops", "control_flow", "ControlFlow"],
            )
            && decl.item_meta.diagnostic_item.as_deref() == Some("ControlFlow")
            && self.option_residual(residual))
        .then_some(output)
    }
    /// Which of `branch` and `from_residual` on `Option` a call calls, if
    /// either: the library's own `impl Try for Option<T>` or `impl
    /// FromResidual<Option<!>> for Option<T>`, at their declared signatures.
    fn try_call(&self, call: &a::Call) -> Result<Option<TryCall>, String> {
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let Ok(id) = self.resolve(ptr) else {
            return Ok(None);
        };
        let Some(callee) = self.krate.fun_decls.get(id) else {
            return Ok(None);
        };
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Ok(None);
        };
        let Some(tr) = self.krate.trait_decls.get(trait_ref.id) else {
            return Ok(None);
        };
        let kind = if path(&tr.item_meta.name, &["core", "ops", "try_trait", "Try"])
            && tr.item_meta.lang_item == Some(LangItem::Try)
        {
            TryCall::Branch
        } else if path(
            &tr.item_meta.name,
            &["core", "ops", "try_trait", "FromResidual"],
        ) {
            TryCall::FromResidual
        } else {
            return Ok(None);
        };
        let (method, implemented) = match kind {
            TryCall::Branch => ("branch", 1),
            TryCall::FromResidual => ("from_residual", 2),
        };
        let name = &callee.item_meta.name.name;
        let Some(imp) = self.krate.trait_impls.get(impl_ref.id) else {
            return Err(unsupported("`?` implementation identity"));
        };
        if tr.item_meta.is_local
            || callee.item_meta.is_local
            || callee.signature.is_unsafe
            || imp.item_meta.is_local
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || !matches!(name.as_slice(), [.., a::PathElem::Ident(last, d)]
                if last == method && *d == a::Disambiguator::ZERO)
            || name[..name.len() - 1] != imp.item_meta.name.name
            || !matches!(imp.item_meta.name.name.as_slice(), [
                a::PathElem::Ident(core, d0),
                a::PathElem::Ident(option, d1),
                a::PathElem::Impl(a::ImplElem::Trait(own)),
            ] if core == "core" && option == "option" && d0.is_zero() && d1.is_zero()
                && *own == impl_ref.id)
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.id != callee.def_id)
            || tr
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.name.0 != method)
            || imp.generics.types.len() != 1
            || !callee.generics.const_generics.is_empty()
            || !ptr.generics.const_generics.is_empty()
            || imp.impl_trait.generics.types.len() != implemented
            || !self.option_of(&imp.impl_trait.generics.types[0], bound_parameter)
            || (kind == TryCall::FromResidual
                && !self.option_residual(&imp.impl_trait.generics.types[1]))
        {
            return Err(unsupported("`?` implementation identity"));
        }
        let [input] = callee.signature.inputs.as_slice() else {
            return Err(unsupported("`?` call signature"));
        };
        let output = &callee.signature.output;
        let declared = match kind {
            TryCall::Branch => {
                self.option_of(input, bound_parameter)
                    && self
                        .option_control_flow(output)
                        .is_some_and(bound_parameter)
            }
            TryCall::FromResidual => {
                self.option_residual(input) && self.option_of(output, bound_parameter)
            }
        };
        if !declared || call.args.len() != 1 {
            return Err(unsupported("`?` call signature"));
        }
        Ok(Some(kind))
    }
    /// `body` with each `?` on an `Option` rewritten to the `match` it
    /// means, or `None` when it has none.
    pub(super) fn option_try_body(
        &self,
        body: &u::ExprBody,
    ) -> Result<Option<u::ExprBody>, String> {
        // Each flow, `flow = branch(o)`, with the option type it becomes.
        let mut flows = BTreeMap::new();
        for block in &body.body {
            if let u::TerminatorKind::Call { call, .. } = &block.terminator.kind
                && self.try_call(call)? == Some(TryCall::Branch)
            {
                let (Some(local), [a::Operand::Move(source) | a::Operand::Copy(source)]) =
                    (call.dest.as_local(), call.args.as_slice())
                else {
                    return Err(unsupported("`?` operand or destination"));
                };
                let payload = self
                    .option_control_flow(&call.dest.ty)
                    .ok_or_else(|| unsupported("`?` destination type"))?;
                if !self.option_of(&source.ty, |p| p == payload)
                    || (self.option_payload(&source.ty).is_none()
                        && self.option_box_payload(&source.ty).is_none())
                    || flows
                        .insert(local, source.ty.clone())
                        .is_some_and(|ty| ty != source.ty)
                {
                    return Err(unsupported("`?` operand type"));
                }
            }
        }
        if flows.is_empty() {
            return Ok(None);
        }
        let residuals: BTreeSet<a::LocalId> = body
            .locals
            .locals
            .iter()
            .filter(|local| self.option_residual(&local.ty))
            .map(|local| local.index)
            .collect();
        // The locals holding a flow's discriminant, `d = @discriminant(flow)`.
        let mut discriminants = BTreeSet::new();
        for block in &body.body {
            for statement in &block.statements {
                if let u::StatementKind::Assign(target, a::Rvalue::Discriminant(place)) =
                    &statement.kind
                    && place.as_local().is_some_and(|l| flows.contains_key(&l))
                    && !target
                        .as_local()
                        .is_some_and(|local| discriminants.insert(local))
                {
                    return Err(unsupported("`?` discriminant"));
                }
            }
        }
        // A use of these locals other than the ones rewritten below is
        // refused.
        let forbidden = |item: &dyn Fn(&mut dyn FnMut(&a::LocalId))| {
            let mut found = false;
            item(&mut |local| {
                found |= flows.contains_key(local)
                    || residuals.contains(local)
                    || discriminants.contains(local);
            });
            found
        };
        let field_of = |place: &a::Place, variant: usize| {
            matches!(&place.kind,
                a::PlaceKind::Projection(inner, a::ProjectionElem::Field(Some(v), field))
                    if inner.as_local().is_some_and(|l| flows.contains_key(&l))
                        && v.index() == variant && field.index() == 0)
        };
        let mut body = body.clone();
        for (local, option) in &flows {
            body.locals.locals[*local].ty = option.clone();
        }
        for local in &residuals {
            body.locals.locals[*local].ty = a::Ty::mk_unit();
        }
        for block in body.body.iter_mut() {
            let mut statements = Vec::with_capacity(block.statements.len());
            for mut statement in std::mem::take(&mut block.statements) {
                let mut unchecked = false;
                match &mut statement.kind {
                    u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                        if residuals.contains(local) =>
                    {
                        continue;
                    }
                    u::StatementKind::StorageLive(_) | u::StatementKind::StorageDead(_) => {}
                    // `residual = copy (flow as Break).0` and its copies hold
                    // `None`; the `from_residual` they reach is `None`.
                    u::StatementKind::Assign(
                        target,
                        a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
                    ) if target.as_local().is_some_and(|l| residuals.contains(&l)) => {
                        if !field_of(source, 1)
                            && !source.as_local().is_some_and(|l| residuals.contains(&l))
                        {
                            return Err(unsupported("`?` residual use"));
                        }
                        continue;
                    }
                    u::StatementKind::Assign(target, a::Rvalue::Discriminant(place))
                        if place.as_local().is_some_and(|l| flows.contains_key(&l)) =>
                    {
                        debug_assert!(target.as_local().is_some());
                        place.ty = flows[&place.as_local().unwrap()].clone();
                    }
                    // `copy (flow as Continue).0` is `Some`'s payload.
                    u::StatementKind::Assign(
                        target,
                        a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
                    ) if field_of(source, 0) => {
                        if forbidden(&|visit| target.dyn_visit(|l: &a::LocalId| visit(l))) {
                            return Err(unsupported("`?` result use"));
                        }
                        let a::PlaceKind::Projection(inner, a::ProjectionElem::Field(variant, _)) =
                            &mut source.kind
                        else {
                            unreachable!()
                        };
                        inner.ty = flows[&inner.as_local().unwrap()].clone();
                        *variant = Some(a::VariantId::from_usize(1));
                    }
                    _ => unchecked = true,
                }
                if unchecked && forbidden(&|visit| statement.dyn_visit(|l: &a::LocalId| visit(l))) {
                    return Err(unsupported("`?` result use"));
                }
                statements.push(statement);
            }
            block.statements = statements;
            let span = block.terminator.span;
            let mut unchecked = false;
            match &mut block.terminator.kind {
                u::TerminatorKind::Call { call, target, .. } => match self.try_call(call)? {
                    // `flow = branch(o)` is `flow = o`.
                    Some(TryCall::Branch) => {
                        let mut destination = call.dest.clone();
                        destination.ty = flows[&destination.as_local().unwrap()].clone();
                        block.statements.push(u::Statement::new(
                            span,
                            u::StatementKind::Assign(
                                destination,
                                a::Rvalue::Use(call.args[0].clone(), a::WithRetag::No),
                            ),
                        ));
                        block.terminator.kind = u::TerminatorKind::Goto { target: *target };
                    }
                    // `x = from_residual(residual)` is `x = None`.
                    Some(TryCall::FromResidual) => {
                        let [a::Operand::Move(source) | a::Operand::Copy(source)] =
                            call.args.as_slice()
                        else {
                            return Err(unsupported("`?` residual use"));
                        };
                        let a::TyKind::Adt(option) = call.dest.ty.kind() else {
                            return Err(unsupported("`?` result type"));
                        };
                        if !source.as_local().is_some_and(|l| residuals.contains(&l))
                            || self.option_payload(&call.dest.ty).is_none()
                            || forbidden(&|visit| call.dest.dyn_visit(|l: &a::LocalId| visit(l)))
                        {
                            return Err(unsupported("`?` residual use"));
                        }
                        block.statements.push(u::Statement::new(
                            span,
                            u::StatementKind::Assign(
                                call.dest.clone(),
                                a::Rvalue::Aggregate(
                                    a::AggregateKind::Adt(
                                        option.clone(),
                                        Some(a::VariantId::from_usize(0)),
                                        None,
                                    ),
                                    Vec::new(),
                                ),
                            ),
                        ));
                        block.terminator.kind = u::TerminatorKind::Goto { target: *target };
                    }
                    None => unchecked = true,
                },
                // A `match` on the flow's discriminant is one on the
                // option's: `Continue`, 0, is `Some`, 1, and `Break`, 1, is
                // `None`, 0.
                u::TerminatorKind::Switch { data, .. }
                    if matches!(&data.scrutinee,
                        a::SwitchScrutinee::Value(a::Operand::Move(p) | a::Operand::Copy(p))
                            if p.as_local().is_some_and(|l| discriminants.contains(&l))) =>
                {
                    for (constant, _) in &mut data.branches {
                        let a::ConstantExprKind::Integer(a::IntegerValue::Signed(
                            a::IntTy::Isize,
                            value @ (0 | 1),
                        )) = *constant.kind()
                        else {
                            return Err(unsupported("`?` switch constant"));
                        };
                        *constant = a::ConstantExpr::new(
                            a::ConstantExprKind::Integer(a::IntegerValue::Signed(
                                a::IntTy::Isize,
                                1 - value,
                            )),
                            constant.ty().clone(),
                        );
                    }
                }
                _ => unchecked = true,
            }
            if unchecked
                && forbidden(&|visit| block.terminator.dyn_visit(|l: &a::LocalId| visit(l)))
            {
                return Err(unsupported("`?` result use"));
            }
        }
        Ok(Some(body))
    }
}
