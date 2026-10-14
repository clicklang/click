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
    pub(super) fn closure_impl_path(&self, imp: &a::TraitImpl) -> Option<&'a [a::PathElem]> {
        let a::TyKind::Adt(r) = imp.impl_trait.generics.types.first()?.kind() else {
            return None;
        };
        let krate: &'a a::TranslatedCrate = self.krate;
        let state = krate.type_decls.get(r.id)?;
        matches!(state.src, a::TypeSource::Closure { .. })
            .then_some(state.item_meta.name.name.as_slice())
    }
}

/// A closure's `Fn::call` body as a function of the closure's parameters.
/// The body takes `&self` and its arguments as one tuple, and first binds
/// each tuple field to the parameter's local, `y = move tupled_args.0`.
/// Those bindings go, the parameter locals become the arguments, and
/// neither `self` nor the tuple may be used otherwise: the closure captures
/// nothing.
pub(super) fn closure_call_body(body: &u::ExprBody) -> Result<u::ExprBody, String> {
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
    // A parameter's storage is the argument's: it is never started or ended.
    for block in body.body.iter_mut() {
        block.statements.retain(|statement| {
            !matches!(statement.kind,
                u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                    if parameters.contains(&local))
        });
    }
    let mut used = false;
    for block in body.body.iter() {
        for statement in &block.statements {
            statement.dyn_visit(|local: &a::LocalId| used |= *local == state || *local == tuple);
        }
        block
            .terminator
            .dyn_visit(|local: &a::LocalId| used |= *local == state || *local == tuple);
    }
    if used {
        return Err(unsupported("closure that uses its state or argument tuple"));
    }
    // Locals in their new order: the result, the parameters, the rest.
    let order = std::iter::once(a::LocalId::ZERO)
        .chain(parameters.iter().copied())
        .chain(
            body.locals
                .locals
                .iter()
                .map(|local| local.index)
                .filter(|index| index.index() > 2 && !parameters.contains(index)),
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
        arg_count: parameters.len(),
        locals,
    };
    Ok(body)
}

/// The parameter types of a closure's `Fn::call`, whose signature takes
/// `&self` and the arguments as one tuple.
pub(super) fn closure_parameter_types(signature: &a::FunSig) -> Result<Vec<a::Ty>, String> {
    let [_, arguments] = signature.inputs.as_slice() else {
        return Err(unsupported("closure call arity"));
    };
    match arguments.kind() {
        a::TyKind::Adt(r) if r.builtin == Some(a::BuiltinAdt::Tuple) => {
            Ok(r.generics.types.iter().cloned().collect())
        }
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
