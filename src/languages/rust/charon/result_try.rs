//! The `?` operator on a `Result`, rewritten to the `match` it means.
//!
//! `r?` calls `<Result<T, E> as Try>::branch(r)`, matches the resulting
//! `ControlFlow<Result<!, E>, T>`, and on `Break(residual)` returns
//! `<Result<U, F> as FromResidual<Result<!, E>>>::from_residual(residual)`.
//! (The library spells the residual's `Ok` type `Infallible`; the compiler
//! hands it over as `!`. Either is accepted.)
//! The library defines `branch(Ok(v))` as `Continue(v)`, `branch(Err(e))` as
//! `Break(Err(e))`, and `from_residual(Err(e))` as `Err(From::from(e))`. So
//! the `ControlFlow` local is the result itself, its `Continue` field is
//! `Ok`'s, the residual is that same `Err`, and the call on the `Break` edge
//! is `Err` of its payload. Only a `?` that keeps the error type, `F == E`,
//! is read: there `From::from` is the identity `impl<T> From<T> for T`. A
//! conversion to another error type is refused.
//!
//! The two discriminants agree: `Continue` and `Ok` are 0, `Break` and `Err`
//! are 1, so the switch on the flow's discriminant is the result's.
use super::protocol::path;
use super::*;

/// One of the two library functions a `?` on a `Result` calls.
#[derive(Clone, Copy, PartialEq)]
enum ResultTryCall {
    Branch,
    FromResidual,
}

/// Whether `ty` is the impl's type parameter number `index`.
fn bound(ty: &a::Ty, index: usize) -> bool {
    matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id))
        if depth.index == 0 && id.index() == index)
}

impl Adapter<'_> {
    /// The `Ok` and `Err` types of a `core::result::Result<O, E>`, whatever
    /// they are.
    fn result_arguments<'t>(&self, ty: &'t a::Ty) -> Option<(&'t a::Ty, &'t a::Ty)> {
        let a::TyKind::Adt(r) = ty.kind() else {
            return None;
        };
        let decl = self.krate.type_decls.get(r.id)?;
        let [ok, err] = r.generics.types.as_raw_slice() else {
            return None;
        };
        (r.builtin.is_none()
            && !decl.item_meta.is_local
            && path(&decl.item_meta.name, &["core", "result", "Result"]))
        .then_some((ok, err))
    }
    /// Whether `ty` is `!` or `core::convert::Infallible`, the uninhabited
    /// `Ok` type of a residual.
    fn infallible(&self, ty: &a::Ty) -> bool {
        matches!(ty.kind(), a::TyKind::Never)
            || matches!(ty.kind(), a::TyKind::Adt(r) if r.builtin.is_none()
            && self.krate.type_decls.get(r.id).is_some_and(|decl| !decl.item_meta.is_local
                && path(&decl.item_meta.name, &["core", "convert", "Infallible"])))
    }
    /// The `E` of `Result<Infallible, E>`, the residual of a `?` on a
    /// `Result`.
    fn result_residual_error<'t>(&self, ty: &'t a::Ty) -> Option<&'t a::Ty> {
        let (ok, err) = self.result_arguments(ty)?;
        self.infallible(ok).then_some(err)
    }
    /// The residual and output of a `ControlFlow<Result<Infallible, E>, C>`.
    fn result_control_flow<'t>(&self, ty: &'t a::Ty) -> Option<(&'t a::Ty, &'t a::Ty)> {
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
            && self.result_residual_error(residual).is_some())
        .then_some((residual, output))
    }
    /// Whether `call` calls `Try::branch` or `FromResidual::from_residual` of
    /// an impl declared in `core::result`. The `Option` rewrite leaves these
    /// to this one.
    pub(super) fn calls_result_try(&self, call: &a::Call) -> bool {
        let a::FnOperand::Regular(ptr) = &call.func else {
            return false;
        };
        let Ok(id) = self.resolve(ptr) else {
            return false;
        };
        let Some(callee) = self.krate.fun_decls.get(id) else {
            return false;
        };
        let a::FunSource::TraitImpl { impl_ref, .. } = &callee.src else {
            return false;
        };
        self.krate.trait_impls.get(impl_ref.id).is_some_and(|imp| {
            matches!(imp.item_meta.name.name.as_slice(), [
                a::PathElem::Ident(core, _),
                a::PathElem::Ident(result, _),
                a::PathElem::Impl(_),
            ] if core == "core" && result == "result")
        })
    }
    /// Which of `branch` and `from_residual` on `Result` a call calls, if
    /// either: the library's own `impl Try for Result<T, E>` or `impl
    /// FromResidual<Result<Infallible, E>> for Result<T, F>`, at their
    /// declared signatures.
    fn result_try_call(&self, call: &a::Call) -> Result<Option<ResultTryCall>, String> {
        if !self.calls_result_try(call) {
            return Ok(None);
        }
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let id = self.resolve(ptr)?;
        let callee = &self.krate.fun_decls[id];
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
            ResultTryCall::Branch
        } else if path(
            &tr.item_meta.name,
            &["core", "ops", "try_trait", "FromResidual"],
        ) {
            ResultTryCall::FromResidual
        } else {
            return Ok(None);
        };
        // `impl<T, E> Try for Result<T, E>`, and `impl<T, E, F: From<E>>
        // FromResidual<Result<Infallible, E>> for Result<T, F>`.
        let (method, parameters, implemented) = match kind {
            ResultTryCall::Branch => ("branch", 2, 1),
            ResultTryCall::FromResidual => ("from_residual", 3, 2),
        };
        let name = &callee.item_meta.name.name;
        let imp = &self.krate.trait_impls[impl_ref.id];
        let own_impl = matches!(imp.item_meta.name.name.as_slice(), [
                a::PathElem::Ident(_, d0),
                a::PathElem::Ident(_, d1),
                a::PathElem::Impl(a::ImplElem::Trait(own)),
            ] if d0.is_zero() && d1.is_zero() && *own == impl_ref.id);
        let self_type = imp.impl_trait.generics.types.as_raw_slice().first();
        let self_declared = self_type
            .and_then(|ty| self.result_arguments(ty))
            .is_some_and(|(ok, err)| match kind {
                ResultTryCall::Branch => bound(ok, 0) && bound(err, 1),
                ResultTryCall::FromResidual => bound(ok, 0) && bound(err, 2),
            });
        let residual_declared = kind == ResultTryCall::Branch
            || imp
                .impl_trait
                .generics
                .types
                .as_raw_slice()
                .get(1)
                .and_then(|ty| self.result_residual_error(ty))
                .is_some_and(|err| bound(err, 1));
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
            || !own_impl
            || imp
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.id != callee.def_id)
            || tr
                .methods
                .get(*item_id)
                .is_none_or(|m| m.skip_binder.name.0 != method)
            || imp.generics.types.len() != parameters
            || !callee.generics.const_generics.is_empty()
            || !ptr.generics.const_generics.is_empty()
            || imp.impl_trait.generics.types.len() != implemented
            || !self_declared
            || !residual_declared
        {
            return Err(unsupported("`?` on a `Result` implementation identity"));
        }
        let [input] = callee.signature.inputs.as_slice() else {
            return Err(unsupported("`?` on a `Result` call signature"));
        };
        let output = &callee.signature.output;
        let declared = match kind {
            ResultTryCall::Branch => {
                self.result_arguments(input)
                    .is_some_and(|(ok, err)| bound(ok, 0) && bound(err, 1))
                    && self
                        .result_control_flow(output)
                        .is_some_and(|(residual, output)| {
                            bound(output, 0)
                                && self
                                    .result_residual_error(residual)
                                    .is_some_and(|err| bound(err, 1))
                        })
            }
            ResultTryCall::FromResidual => {
                self.result_residual_error(input)
                    .is_some_and(|err| bound(err, 1))
                    && self
                        .result_arguments(output)
                        .is_some_and(|(ok, err)| bound(ok, 0) && bound(err, 2))
            }
        };
        if !declared || call.args.len() != 1 {
            return Err(unsupported("`?` on a `Result` call signature"));
        }
        Ok(Some(kind))
    }
    /// `body` with each `?` on a `Result` rewritten to the `match` it
    /// means, or `None` when it has none.
    pub(super) fn result_try_body(
        &self,
        body: &u::ExprBody,
    ) -> Result<Option<u::ExprBody>, String> {
        // Each flow, `flow = branch(r)`, with the result type it becomes.
        let mut flows: BTreeMap<a::LocalId, a::Ty> = BTreeMap::new();
        for block in &body.body {
            if let u::TerminatorKind::Call { call, .. } = &block.terminator.kind
                && self.result_try_call(call)? == Some(ResultTryCall::Branch)
            {
                let (Some(local), [a::Operand::Move(source) | a::Operand::Copy(source)]) =
                    (call.dest.as_local(), call.args.as_slice())
                else {
                    return Err(unsupported("`?` operand or destination"));
                };
                let (residual, output) = self
                    .result_control_flow(&call.dest.ty)
                    .ok_or_else(|| unsupported("`?` destination type"))?;
                let matches_source = self.result_arguments(&source.ty).is_some_and(|(ok, err)| {
                    ok == output && self.result_residual_error(residual) == Some(err)
                });
                if !matches_source
                    || self.result_payloads(&source.ty).is_none()
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
        let field_of = |place: &a::Place, variant: usize| -> Option<a::LocalId> {
            match &place.kind {
                a::PlaceKind::Projection(inner, a::ProjectionElem::Field(Some(v), field))
                    if v.index() == variant && field.index() == 0 =>
                {
                    inner.as_local().filter(|l| flows.contains_key(l))
                }
                _ => None,
            }
        };
        // Each residual local, `residual = (flow as Break).0` or a copy of
        // another, with the result type it becomes: the flow's.
        let mut residuals: BTreeMap<a::LocalId, a::Ty> = BTreeMap::new();
        loop {
            let before = residuals.len();
            for block in &body.body {
                for statement in &block.statements {
                    if let u::StatementKind::Assign(
                        target,
                        a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
                    ) = &statement.kind
                        && let Some(target) = target.as_local()
                        && self
                            .result_residual_error(&body.locals.locals[target].ty)
                            .is_some()
                    {
                        let ty = if let Some(flow) = field_of(source, 1) {
                            flows[&flow].clone()
                        } else if let Some(ty) = source.as_local().and_then(|l| residuals.get(&l)) {
                            ty.clone()
                        } else {
                            continue;
                        };
                        if residuals
                            .insert(target, ty.clone())
                            .is_some_and(|t| t != ty)
                        {
                            return Err(unsupported("`?` residual use"));
                        }
                    }
                }
            }
            if residuals.len() == before {
                break;
            }
        }
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
                    || residuals.contains_key(local)
                    || discriminants.contains(local);
            });
            found
        };
        let mut body = body.clone();
        for (local, result) in flows.iter().chain(&residuals) {
            body.locals.locals[*local].ty = result.clone();
        }
        let retyped = |place: &mut a::Place| {
            if let Some(local) = place.as_local()
                && let Some(ty) = flows.get(&local).or_else(|| residuals.get(&local))
            {
                place.ty = ty.clone();
            }
        };
        for block in body.body.iter_mut() {
            for statement in block.statements.iter_mut() {
                let mut unchecked = false;
                match &mut statement.kind {
                    u::StatementKind::StorageLive(_) | u::StatementKind::StorageDead(_) => {}
                    // `residual = copy (flow as Break).0` is the flow itself,
                    // the `Err` it holds; a copy of a residual stays one.
                    u::StatementKind::Assign(
                        target,
                        a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
                    ) if target
                        .as_local()
                        .is_some_and(|l| residuals.contains_key(&l)) =>
                    {
                        if let Some(flow) = field_of(source, 1) {
                            *source = a::Place::new(flow, flows[&flow].clone());
                        } else if !source
                            .as_local()
                            .is_some_and(|l| residuals.contains_key(&l))
                        {
                            return Err(unsupported("`?` residual use"));
                        }
                        retyped(source);
                        retyped(target);
                    }
                    u::StatementKind::Assign(target, a::Rvalue::Discriminant(place))
                        if place.as_local().is_some_and(|l| flows.contains_key(&l)) =>
                    {
                        debug_assert!(target.as_local().is_some());
                        retyped(place);
                    }
                    // `copy (flow as Continue).0` is `Ok`'s payload: both are
                    // variant 0.
                    u::StatementKind::Assign(
                        target,
                        a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
                    ) if field_of(source, 0).is_some() => {
                        if forbidden(&|visit| target.dyn_visit(|l: &a::LocalId| visit(l))) {
                            return Err(unsupported("`?` result use"));
                        }
                        let a::PlaceKind::Projection(inner, _) = &mut source.kind else {
                            unreachable!()
                        };
                        retyped(inner);
                    }
                    _ => unchecked = true,
                }
                if unchecked && forbidden(&|visit| statement.dyn_visit(|l: &a::LocalId| visit(l))) {
                    return Err(unsupported("`?` result use"));
                }
            }
            let span = block.terminator.span;
            let mut unchecked = false;
            match &mut block.terminator.kind {
                u::TerminatorKind::Call { call, target, .. } => match self.result_try_call(call)? {
                    // `flow = branch(r)` is `flow = r`.
                    Some(ResultTryCall::Branch) => {
                        let mut destination = call.dest.clone();
                        retyped(&mut destination);
                        block.statements.push(u::Statement::new(
                            span,
                            u::StatementKind::Assign(
                                destination,
                                a::Rvalue::Use(call.args[0].clone(), a::WithRetag::No),
                            ),
                        ));
                        block.terminator.kind = u::TerminatorKind::Goto { target: *target };
                    }
                    // `x = from_residual(residual)` is `x = Err((residual as
                    // Err).0)` when `x`'s error type is the residual's.
                    Some(ResultTryCall::FromResidual) => {
                        let [a::Operand::Move(source) | a::Operand::Copy(source)] =
                            call.args.as_slice()
                        else {
                            return Err(unsupported("`?` residual use"));
                        };
                        let Some(residual) = source.as_local().and_then(|l| residuals.get(&l))
                        else {
                            return Err(unsupported("`?` residual use"));
                        };
                        let a::TyKind::Adt(result) = call.dest.ty.kind() else {
                            return Err(unsupported("`?` result type"));
                        };
                        let kept_error = self
                            .result_arguments(&call.dest.ty)
                            .zip(self.result_arguments(residual))
                            .is_some_and(|((_, to), (_, from))| to == from);
                        if !kept_error {
                            return Err(unsupported(
                                "`?` that converts the error type with `From`",
                            ));
                        }
                        if self.result_payloads(&call.dest.ty).is_none()
                            || forbidden(&|visit| call.dest.dyn_visit(|l: &a::LocalId| visit(l)))
                        {
                            return Err(unsupported("`?` residual use"));
                        }
                        let (_, error) = self.result_arguments(residual).unwrap();
                        let payload = a::Place::new(source.as_local().unwrap(), residual.clone())
                            .project(
                                a::ProjectionElem::Field(
                                    Some(a::VariantId::from_usize(1)),
                                    a::FieldId::from_usize(0),
                                ),
                                error.clone(),
                            );
                        block.statements.push(u::Statement::new(
                            span,
                            u::StatementKind::Assign(
                                call.dest.clone(),
                                a::Rvalue::Aggregate(
                                    a::AggregateKind::Adt(
                                        result.clone(),
                                        Some(a::VariantId::from_usize(1)),
                                        None,
                                    ),
                                    vec![a::Operand::Move(payload)],
                                ),
                            ),
                        ));
                        block.terminator.kind = u::TerminatorKind::Goto { target: *target };
                    }
                    None => unchecked = true,
                },
                // A `match` on the flow's discriminant is one on the
                // result's: `Continue` and `Ok` are 0, `Break` and `Err` 1.
                u::TerminatorKind::Switch { data, .. }
                    if matches!(&data.scrutinee,
                        a::SwitchScrutinee::Value(a::Operand::Move(p) | a::Operand::Copy(p))
                            if p.as_local().is_some_and(|l| discriminants.contains(&l))) =>
                {
                    for (constant, _) in &data.branches {
                        if !matches!(
                            *constant.kind(),
                            a::ConstantExprKind::Integer(a::IntegerValue::Signed(
                                a::IntTy::Isize,
                                0 | 1,
                            ))
                        ) {
                            return Err(unsupported("`?` switch constant"));
                        }
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
