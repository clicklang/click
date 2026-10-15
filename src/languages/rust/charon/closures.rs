//! Closures that capture nothing, passed for a `fn` pointer. Charon writes
//! `apply(|y| y + y, x)` as a closure state type with no fields, the closure's
//! `Fn::call` method taking `&self` and its arguments as one tuple, and a
//! generated `ClosureAsFn` function the pointer cast names. The importer
//! keeps only the `call` body, named as rustc names the closure
//! (`caller::{closure#0}`) and rewritten as an ordinary function of the
//! closure's parameters, and a cast of the generated function is the
//! address of that function.
use super::*;

impl Adapter<'_> {
    /// The name of the closure whose `ClosureAsFn` function `f` is, when it is
    /// one.
    pub(super) fn closure_as_fn_name(&self, f: &a::FunDecl) -> Result<Option<String>, String> {
        let path = &f.item_meta.name.name;
        let Some((a::PathElem::Builtin(a::BuiltinPathElem::ClosureAsFn, _), closure)) =
            path.split_last()
        else {
            return Ok(None);
        };
        self.closure_name(closure).map(Some)
    }

    /// The name of a closure from its path, which ends in its closure element.
    pub(super) fn closure_name(&self, path: &[a::PathElem]) -> Result<String, String> {
        if !matches!(
            path.last(),
            Some(a::PathElem::Builtin(a::BuiltinPathElem::Closure, _))
        ) {
            return Err(unsupported("closure path"));
        }
        self.qualified_function_name(&a::Name {
            name: path.to_vec(),
        })
    }
}

impl<'a> Adapter<'a> {
    /// Whether `id` is the state of a closure that captures nothing.
    pub(super) fn empty_closure_state(&self, id: a::TypeDeclId) -> bool {
        self.krate.type_decls.get(id).is_some_and(|state| {
            matches!(state.src, a::TypeSource::Closure { .. })
                && matches!(&state.kind, a::TypeDeclKind::Struct(fields) if fields.is_empty())
        })
    }

    /// The path of the closure a `Fn`, `FnMut` or `FnOnce` implementation is
    /// for, `caller::{closure#0}`: the name of its self type, the closure's
    /// state.
    pub(super) fn closure_impl_path(
        &self,
        imp: &a::TraitImpl,
    ) -> Option<(&'a [a::PathElem], a::TypeDeclId)> {
        let a::TyKind::Adt(r) = imp.impl_trait.generics.types.first()?.kind() else {
            return None;
        };
        let krate: &'a a::TranslatedCrate = self.krate;
        let state = krate.type_decls.get(r.id)?;
        matches!(state.src, a::TypeSource::Closure { .. })
            .then_some((state.item_meta.name.name.as_slice(), r.id))
    }
}

/// A variable a closure captures, as the closure's creation names it: by
/// shared reference (`|y| y + k` borrows `k`) or by value (`move`).
#[derive(Clone)]
pub(super) struct Capture {
    pub(super) name: String,
    /// The captured variable's own type.
    pub(super) ty: a::Ty,
    pub(super) by_reference: bool,
}

/// A closure's `Fn::call` body as a function of its captures, then its
/// parameters. The body takes `&self` and its arguments as one tuple, and
/// first binds each tuple field to the parameter's local, `y = move
/// tupled_args.0`. Those bindings go, and the parameter locals become the
/// arguments. A capture by reference is read as `t = copy (*self).i` then
/// `*t`, and one by value as `(*self).i`; each becomes a read of a new
/// leading parameter named for the captured variable. Neither `self` nor
/// the tuple may be used otherwise.
pub(super) fn closure_call_body(
    body: &u::ExprBody,
    captures: &[Capture],
) -> Result<u::ExprBody, String> {
    let state = a::LocalId::from_usize(1);
    let tuple = a::LocalId::from_usize(2);
    if body.locals.arg_count != 2 {
        return Err(unsupported("closure call arity"));
    }
    let arity = match body.locals.locals[tuple].ty.kind() {
        a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Tuple) => r.generics.types.len(),
        _ => return Err(unsupported("closure arguments other than a tuple")),
    };
    let mut body = body.clone();
    let first_capture = body.locals.locals.len();
    let capture_locals = (0..captures.len())
        .map(|index| a::LocalId::from_usize(first_capture + index))
        .collect::<Vec<_>>();
    for (capture, local) in captures.iter().zip(&capture_locals) {
        body.locals.locals.push(a::Local {
            index: *local,
            name: Some(capture.name.clone()),
            span: body.span,
            ty: capture.ty.clone(),
            drop_flag_for: None,
        });
    }
    // `t = copy (*self).i`: `t` is the reference capture `i` holds.
    let mut references = BTreeMap::new();
    for block in body.body.iter_mut() {
        let mut statements = Vec::with_capacity(block.statements.len());
        for statement in std::mem::take(&mut block.statements) {
            if let u::StatementKind::Assign(
                target,
                a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _),
            ) = &statement.kind
                && let a::PlaceKind::Local(reference) = target.kind
                && let Some(field) = state_field(source, state)
                && captures
                    .get(field)
                    .is_some_and(|capture| capture.by_reference)
            {
                if references
                    .insert(reference, capture_locals[field])
                    .is_some()
                {
                    return Err(unsupported("closure capture reference read twice"));
                }
                continue;
            }
            statements.push(statement);
        }
        block.statements = statements;
    }
    let rewrite = |place: &mut a::Place| {
        let replacement = match &place.kind {
            a::PlaceKind::Projection(inner, a::ProjectionElem::Deref) => match inner.kind {
                a::PlaceKind::Local(reference) => references.get(&reference).copied(),
                _ => None,
            },
            _ => state_field(place, state)
                .filter(|field| {
                    captures
                        .get(*field)
                        .is_some_and(|capture| !capture.by_reference)
                })
                .map(|field| capture_locals[field]),
        };
        if let Some(local) = replacement {
            place.kind = a::PlaceKind::Local(local);
        }
    };
    for block in body.body.iter_mut() {
        for statement in &mut block.statements {
            statement.dyn_visit_mut(rewrite);
        }
        block.terminator.dyn_visit_mut(rewrite);
    }
    let entry = body
        .body
        .iter_mut()
        .next()
        .ok_or_else(|| unsupported("closure without a body"))?;
    let mut parameters: Vec<Option<a::LocalId>> = vec![None; arity];
    let mut statements = Vec::with_capacity(entry.statements.len());
    for statement in std::mem::take(&mut entry.statements) {
        if let Some((field, local)) = tuple_field_binding(&statement, tuple) {
            let slot = parameters
                .get_mut(field)
                .ok_or_else(|| unsupported("closure argument field"))?;
            if slot.replace(local).is_some() {
                return Err(unsupported("closure argument bound twice"));
            }
            continue;
        }
        statements.push(statement);
    }
    entry.statements = statements;
    let parameters = parameters
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| unsupported("closure argument without a named binding"))?;
    // A parameter's storage is the argument's: it is never started or ended,
    // and a capture reference is gone.
    for block in body.body.iter_mut() {
        block.statements.retain(|statement| {
            !matches!(statement.kind,
                u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                    if parameters.contains(&local) || references.contains_key(&local))
        });
    }
    let mut used = false;
    for block in body.body.iter() {
        for statement in &block.statements {
            statement.dyn_visit(|local: &a::LocalId| {
                used |= *local == state || *local == tuple || references.contains_key(local)
            });
        }
        block.terminator.dyn_visit(|local: &a::LocalId| {
            used |= *local == state || *local == tuple || references.contains_key(local)
        });
    }
    if used {
        return Err(unsupported(
            "closure that uses its state or argument tuple otherwise",
        ));
    }
    // Locals in their new order: the result, the captures, the parameters,
    // the rest.
    let order = std::iter::once(a::LocalId::ZERO)
        .chain(capture_locals.iter().copied())
        .chain(parameters.iter().copied())
        .chain(
            body.locals
                .locals
                .iter()
                .map(|local| local.index)
                .filter(|index| {
                    index.index() > 2
                        && index.index() < first_capture
                        && !parameters.contains(index)
                        && !references.contains_key(index)
                }),
        )
        .collect::<Vec<_>>();
    let mut renumbered = BTreeMap::new();
    for (new, old) in order.iter().enumerate() {
        renumbered.insert(*old, a::LocalId::from_usize(new));
    }
    for block in body.body.iter_mut() {
        for statement in &mut block.statements {
            statement.dyn_visit_mut(|local: &mut a::LocalId| *local = renumbered[local]);
        }
        block
            .terminator
            .dyn_visit_mut(|local: &mut a::LocalId| *local = renumbered[local]);
    }
    let mut locals = a::IndexVec::new();
    for old in &order {
        let mut local = body.locals.locals[*old].clone();
        if local.drop_flag_for.is_some() {
            return Err(unsupported("closure drop flag"));
        }
        local.index = renumbered[old];
        locals.push(local);
    }
    body.locals = a::Locals {
        arg_count: captures.len() + parameters.len(),
        locals,
    };
    Ok(body)
}

/// The field `i` of the closure state, `(*self).i`, when `place` is one.
fn state_field(place: &a::Place, state: a::LocalId) -> Option<usize> {
    let a::PlaceKind::Projection(inner, a::ProjectionElem::Field(None, field)) = &place.kind else {
        return None;
    };
    (dereferenced_local(inner) == Some(state)).then(|| field.index())
}

/// The parameter types of a closure's `Fn::call`, whose signature takes
/// `&self` and the arguments as one tuple.
pub(super) fn closure_parameter_types(
    signature: &a::FunSig,
    captures: &[Capture],
) -> Result<Vec<a::Ty>, String> {
    let [_, arguments] = signature.inputs.as_slice() else {
        return Err(unsupported("closure call arity"));
    };
    match arguments.kind() {
        a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Tuple) => Ok(captures
            .iter()
            .map(|capture| capture.ty.clone())
            .chain(r.generics.types.iter().cloned())
            .collect()),
        _ => Err(unsupported("closure arguments other than a tuple")),
    }
}

/// `local = move tuple.field` or a copy of it: the field and the local.
fn tuple_field_binding(statement: &u::Statement, tuple: a::LocalId) -> Option<(usize, a::LocalId)> {
    let u::StatementKind::Assign(
        target,
        a::Rvalue::Use(a::Operand::Move(source) | a::Operand::Copy(source), _),
    ) = &statement.kind
    else {
        return None;
    };
    let a::PlaceKind::Local(local) = target.kind else {
        return None;
    };
    let a::PlaceKind::Projection(inner, a::ProjectionElem::Field(None, field)) = &source.kind
    else {
        return None;
    };
    matches!(inner.kind, a::PlaceKind::Local(found) if found == tuple)
        .then(|| (field.index(), local))
}

/// What a body does with closures that capture and with `&dyn Fn` values,
/// in the forms rustc writes them.
///
/// Creating a closure for a `&dyn Fn` parameter builds its state from its
/// captures, takes a reference to it and unsizes that reference:
/// `t = &k; s = {closure} { _0: move t }; r = &s; q = &(*r); x =
/// unsize_cast(move q)`. The importer reads this as one creation of a
/// closure instance in `x` from the captured locals, `k`. A call through a
/// `&dyn Fn` reborrows it and passes its arguments as one tuple:
/// `r = &(*f); a = (move y,); call Fn::call(move r, move a)`, which the
/// importer reads as a call through `r`, a copy of `f`, with `y`.
#[derive(Default)]
pub(super) struct ClosurePlumbing {
    /// Locals that carry only the plumbing: a closure's state, references
    /// to it, the references its state holds, and a call's argument tuple.
    pub(super) elided: BTreeSet<a::LocalId>,
    /// The local each closure creation assigns, with the closure's state
    /// type and its captured locals in field order.
    pub(super) creations: BTreeMap<a::LocalId, (a::TypeDeclId, Vec<a::LocalId>)>,
    /// The operands of each call's argument tuple, by the tuple's local.
    pub(super) dyn_arguments: BTreeMap<a::LocalId, Vec<a::Operand>>,
}

/// `local` when `operand` moves or copies a whole local.
fn whole_local(operand: &a::Operand) -> Option<a::LocalId> {
    match operand {
        a::Operand::Move(place) | a::Operand::Copy(place) => match place.kind {
            a::PlaceKind::Local(local) => Some(local),
            _ => None,
        },
        _ => None,
    }
}

/// The local a place dereferences, `*l`.
fn dereferenced_local(place: &a::Place) -> Option<a::LocalId> {
    match &place.kind {
        a::PlaceKind::Projection(inner, a::ProjectionElem::Deref) => match inner.kind {
            a::PlaceKind::Local(local) => Some(local),
            _ => None,
        },
        _ => None,
    }
}

impl Adapter<'_> {
    /// The parameter and result types of `dyn Fn(A, ...) -> R`.
    pub(super) fn dyn_fn_signature(
        &self,
        predicate: &a::DynPredicate,
    ) -> Result<(Vec<Type>, Type), String> {
        let params = &predicate.binder.params;
        let clauses = params.trait_clauses.iter().collect::<Vec<_>>();
        let [clause] = clauses.as_slice() else {
            return Err(unsupported("dyn trait other than one Fn"));
        };
        let trait_ref = &clause.trait_.skip_binder;
        let trait_decl = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing dyn trait"))?;
        if trait_decl.item_meta.lang_item != Some(LangItem::Fn) {
            return Err(unsupported("dyn trait other than Fn"));
        }
        let Some(arguments) = trait_ref.generics.types.get(1) else {
            return Err(unsupported("dyn Fn arguments"));
        };
        let a::TyKind::Adt(tuple) = arguments.kind() else {
            return Err(unsupported("dyn Fn arguments other than a tuple"));
        };
        if tuple.builtin != Some(a::BuiltinAdt::Tuple) {
            return Err(unsupported("dyn Fn arguments other than a tuple"));
        }
        let parameters = tuple
            .generics
            .types
            .iter()
            .map(|ty| self.ty(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let constraints = params.trait_type_constraints.iter().collect::<Vec<_>>();
        let [output] = constraints.as_slice() else {
            return Err(unsupported("dyn Fn without one output type"));
        };
        let result = self.ty(&output.skip_binder.ty)?;
        Ok((parameters, result))
    }

    /// Whether `ty` is `&dyn Fn(...)`.
    pub(super) fn is_dyn_fn_reference(&self, ty: &a::Ty) -> bool {
        matches!(ty.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Shared)
            if matches!(pointee.kind(), a::TyKind::DynTrait(_)))
    }

    /// The closure creations and `&dyn Fn` calls in `body`.
    pub(super) fn closure_plumbing(&self, body: &u::ExprBody) -> Result<ClosurePlumbing, String> {
        let mut definitions = BTreeMap::new();
        for block in body.body.iter() {
            for statement in &block.statements {
                if let u::StatementKind::Assign(target, value) = &statement.kind
                    && let a::PlaceKind::Local(local) = target.kind
                    && definitions.insert(local, value).is_some()
                {
                    // A local assigned twice is not plumbing; leave it to
                    // the ordinary statements.
                    definitions.insert(local, value);
                }
            }
        }
        let mut plumbing = ClosurePlumbing::default();
        for block in body.body.iter() {
            for statement in &block.statements {
                let u::StatementKind::Assign(target, value) = &statement.kind else {
                    continue;
                };
                let a::PlaceKind::Local(created) = target.kind else {
                    continue;
                };
                let a::Rvalue::UnaryOp(a::UnOp::Cast(a::CastKind::Unsize(..)), source) = value
                else {
                    continue;
                };
                if !self.is_dyn_fn_reference(&target.ty) {
                    continue;
                }
                // `q = &(*r)`, `r = &s`: the references to the state.
                let mut reference = whole_local(source)
                    .ok_or_else(|| unsupported("closure unsized from a non-local"))?;
                let mut chain = vec![reference];
                let state = loop {
                    match definitions.get(&reference) {
                        Some(a::Rvalue::Ref { place, .. }) => {
                            if let Some(inner) = dereferenced_local(place) {
                                reference = inner;
                                chain.push(reference);
                            } else if let a::PlaceKind::Local(state) = place.kind {
                                break state;
                            } else {
                                return Err(unsupported("closure reference to a projection"));
                            }
                        }
                        Some(a::Rvalue::Use(operand, _)) if whole_local(operand).is_some() => {
                            reference = whole_local(operand).expect("matched a whole local");
                            chain.push(reference);
                        }
                        _ => return Err(unsupported("closure reference not built locally")),
                    }
                };
                let Some(a::Rvalue::Aggregate(
                    a::AggregateKind::Adt(state_type, None, None),
                    fields,
                )) = definitions.get(&state)
                else {
                    return Err(unsupported("closure state not built locally"));
                };
                if !matches!(
                    self.krate
                        .type_decls
                        .get(state_type.id)
                        .map(|decl| &decl.src),
                    Some(a::TypeSource::Closure { .. })
                ) {
                    return Err(unsupported("unsized value other than a closure"));
                }
                let mut captures = Vec::new();
                for field in fields {
                    let field_local = whole_local(field)
                        .ok_or_else(|| unsupported("closure capture other than a local"))?;
                    // A capture by shared reference, `t = &k`, or by value.
                    match definitions.get(&field_local) {
                        Some(a::Rvalue::Ref {
                            place,
                            kind: a::BorrowKind::Shared,
                            ..
                        }) => {
                            let a::PlaceKind::Local(captured) = place.kind else {
                                return Err(unsupported("closure capture of a projection"));
                            };
                            plumbing.elided.insert(field_local);
                            captures.push(captured);
                        }
                        Some(a::Rvalue::Ref { .. }) => {
                            return Err(unsupported("closure capture by mutable reference"));
                        }
                        _ => captures.push(field_local),
                    }
                }
                plumbing.elided.insert(state);
                plumbing.elided.extend(chain);
                plumbing
                    .creations
                    .insert(created, (state_type.id, captures));
            }
            // A call through `&dyn Fn` passes its arguments as one tuple.
            if let u::TerminatorKind::Call { call, .. } = &block.terminator.kind
                && let a::FnOperand::Regular(pointer) = &call.func
                && self.is_dyn_fn_call(pointer)
            {
                let [_, tuple] = call.args.as_slice() else {
                    return Err(unsupported("dyn Fn call arity"));
                };
                let tuple = whole_local(tuple)
                    .ok_or_else(|| unsupported("dyn Fn call arguments other than a local"))?;
                let Some(a::Rvalue::Aggregate(a::AggregateKind::Adt(r, None, None), operands)) =
                    definitions.get(&tuple)
                else {
                    return Err(unsupported("dyn Fn call arguments not built locally"));
                };
                if r.builtin != Some(a::BuiltinAdt::Tuple) {
                    return Err(unsupported("dyn Fn call arguments other than a tuple"));
                }
                plumbing.elided.insert(tuple);
                plumbing.dyn_arguments.insert(tuple, operands.clone());
            }
        }
        Ok(plumbing)
    }

    /// Whether `pointer` is `Fn::call` on a `dyn Fn`.
    pub(super) fn is_dyn_fn_call(&self, pointer: &a::FnPtr) -> bool {
        let a::FnPtrKind::Trait(trait_ref, _) = pointer.kind.as_ref() else {
            return false;
        };
        let trait_id = trait_ref.trait_decl_ref.skip_binder.id;
        self.krate
            .trait_decls
            .get(trait_id)
            .is_some_and(|decl| decl.item_meta.lang_item == Some(LangItem::Fn))
            && matches!(
                trait_ref
                    .trait_decl_ref
                    .skip_binder
                    .generics
                    .types
                    .first()
                    .map(|ty| ty.kind()),
                Some(a::TyKind::DynTrait(_))
            )
    }
}

impl BodyAdapter<'_, '_> {
    /// A statement of the closure plumbing: nothing for an elided local, a
    /// closure instance for a creation, and a copy for a `&dyn Fn` reborrow.
    pub(super) fn closure_statement(&self, s: &u::Statement) -> Result<Option<Option<S>>, String> {
        match &s.kind {
            u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                if self.plumbing.elided.contains(local) =>
            {
                Ok(Some(None))
            }
            u::StatementKind::Assign(target, value) => {
                let a::PlaceKind::Local(local) = target.kind else {
                    return Ok(None);
                };
                if self.plumbing.elided.contains(&local) {
                    return Ok(Some(None));
                }
                if let Some((state, captures)) = self.plumbing.creations.get(&local) {
                    let function = self.adapter.closure_state_function(*state)?;
                    let captures = captures
                        .iter()
                        .map(|capture| {
                            Ok(E::Local {
                                name: self.local(*capture)?,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let value_type = self.adapter.ty(&target.ty)?;
                    // A closure that captures nothing is its function.
                    let value = if captures.is_empty() {
                        E::FunctionAddress {
                            function,
                            value_type,
                        }
                    } else {
                        E::ClosureInstance {
                            function,
                            captures,
                            value_type,
                        }
                    };
                    return Ok(Some(Some(S::Assign {
                        target: self.place(target)?,
                        value,
                    })));
                }
                // `r = &(*f)`: a reborrow of a `&dyn Fn` is the same value.
                if self.adapter.is_dyn_fn_reference(&target.ty)
                    && let a::Rvalue::Ref { place, .. } = value
                    && let Some(source) = dereferenced_local(place)
                {
                    return Ok(Some(Some(S::Assign {
                        target: self.place(target)?,
                        value: E::Local {
                            name: self.local(source)?,
                        },
                    })));
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// `Fn::call(move r, move a)` on a `&dyn Fn`: a call through `r` with
    /// the operands of the tuple `a`.
    pub(super) fn dyn_fn_call(&self, call: &a::Call, target: u::BlockId) -> Result<T, String> {
        let [pointer, tuple] = call.args.as_slice() else {
            return Err(unsupported("dyn Fn call arity"));
        };
        let arguments = whole_local(tuple)
            .and_then(|tuple| self.plumbing.dyn_arguments.get(&tuple))
            .ok_or_else(|| unsupported("dyn Fn call arguments"))?;
        self.pointer_call_with(pointer, arguments, call, target)
    }
}

impl Adapter<'_> {
    /// The name of the closure whose state type is `state`.
    pub(super) fn closure_state_function(&self, state: a::TypeDeclId) -> Result<String, String> {
        let decl = self
            .krate
            .type_decls
            .get(state)
            .ok_or_else(|| unsupported("missing closure state"))?;
        self.closure_name(&decl.item_meta.name.name)
    }
}

impl Adapter<'_> {
    /// The variables each closure captures, by its state type, read from the
    /// creations in the crate's bodies. A closure created in two places must
    /// capture variables of the same names and types in both.
    pub(super) fn record_closure_captures(&mut self) -> Result<(), String> {
        let mut found = BTreeMap::<a::TypeDeclId, Vec<Capture>>::new();
        for f in self.krate.fun_decls.iter() {
            if !f.item_meta.is_local {
                continue;
            }
            let a::Body::Unstructured(body) = &f.body else {
                continue;
            };
            for (state, captured) in self.closure_plumbing(body)?.creations.values() {
                let decl = &self.krate.type_decls[*state];
                let a::TypeDeclKind::Struct(fields) = &decl.kind else {
                    return Err(unsupported("closure state other than a struct"));
                };
                let captures = captured
                    .iter()
                    .zip(fields.iter())
                    .map(|(local, field)| {
                        let local = &body.locals.locals[*local];
                        Ok(Capture {
                            name: local.name.clone().ok_or_else(|| {
                                unsupported("closure capture of an unnamed local")
                            })?,
                            ty: local.ty.clone(),
                            by_reference: matches!(field.ty.kind(), a::TyKind::Ref(..)),
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                if let Some(previous) = found.insert(*state, captures.clone())
                    && previous
                        .iter()
                        .map(|c| (&c.name, &c.ty, c.by_reference))
                        .ne(captures.iter().map(|c| (&c.name, &c.ty, c.by_reference)))
                {
                    return Err(unsupported("closure created with different captures"));
                }
            }
        }
        self.closure_captures = found;
        Ok(())
    }
}
