//! Compiler-resolved shared byte split_at, with explicit tuple component storage.
use super::protocol::{local, variable};
use super::*;

fn shared_slice(ty: &a::Ty, template: bool) -> bool {
    matches!(ty.kind(), a::TyKind::Ref(_, pointee, a::RefKind::Shared)
        if matches!(pointee.kind(), a::TyKind::Slice(element, _) if if template { variable(element) } else { byte_slice(pointee) }))
}
impl Adapter<'_> {
    pub(super) fn shared_slice_pair(&self, ty: &a::Ty, template: bool) -> bool {
        let a::TyKind::Adt(r) = ty.kind() else {
            return false;
        };
        let Some(decl) = self.krate.type_decls.get(r.id) else {
            return false;
        };
        r.builtin == Some(a::BuiltinAdt::Tuple)
            && matches!(decl.src, a::TypeSource::Builtin(a::BuiltinAdt::Tuple))
            && !decl.item_meta.is_local
            && matches!(decl.item_meta.name.name.as_slice(), [a::PathElem::Builtin(a::BuiltinPathElem::Tuple(2), d)] if d.is_zero())
            && decl.generics.types.len() == 2
            && decl.generics.regions.is_empty()
            && decl.generics.const_generics.is_empty()
            && matches!(&decl.kind, a::TypeDeclKind::Struct(fields) if fields.len() == 2
                && fields.iter().enumerate().all(|(index, field)|
                    matches!(field.ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 0 && id.index() == index)))
            && r.generics.regions.is_empty()
            && r.generics.const_generics.is_empty()
            && r.generics.types.len() == 2
            && r.generics.types.iter().all(|ty| shared_slice(ty, template))
    }
}
impl BodyAdapter<'_, '_> {
    pub(super) fn slice_pair_statement(&self, s: &u::Statement) -> Result<Option<Vec<S>>, String> {
        if let u::StatementKind::StorageDead(id) = &s.kind
            && let Some(pair) = self.slice_pairs.get(id)
        {
            return Ok(Some(
                pair.iter()
                    .map(|local| S::EndStorage {
                        local: local.clone(),
                    })
                    .collect(),
            ));
        }
        let u::StatementKind::Assign(target, value) = &s.kind else {
            return Ok(None);
        };
        if !self.adapter.shared_slice_pair(&target.ty, false) {
            return Ok(None);
        }
        let a::Rvalue::Use(a::Operand::Copy(source) | a::Operand::Move(source), _) = value else {
            return Err(unsupported(
                "shared slice pair assignment outside complete copy/move",
            ));
        };
        if !self.adapter.shared_slice_pair(&source.ty, false) {
            return Err(unsupported("shared slice pair copy type"));
        }
        let target = self
            .slice_pairs
            .get(&local(target)?)
            .ok_or_else(|| unsupported("shared slice pair destination"))?;
        let source = self
            .slice_pairs
            .get(&local(source)?)
            .ok_or_else(|| unsupported("shared slice pair source"))?;
        // Complete copies preserve component order. The disjoint component
        // slots mean sequential assignments also handle a self-copy safely.
        Ok(Some(
            target
                .iter()
                .zip(source)
                .map(|(target, source)| S::Assign {
                    target: E::Local {
                        name: target.clone(),
                    },
                    value: E::Local {
                        name: source.clone(),
                    },
                })
                .collect(),
        ))
    }
    pub(super) fn slice_pair_projection(&self, p: &a::Place) -> Result<Option<E>, String> {
        let a::PlaceKind::Projection(base, a::ProjectionElem::Field(variant, field)) = &p.kind
        else {
            return Ok(None);
        };
        if !self.adapter.shared_slice_pair(&base.ty, false) {
            return Ok(None);
        }
        let id = local(base)?;
        let pair = self
            .slice_pairs
            .get(&id)
            .ok_or_else(|| unsupported("shared slice pair storage"))?;
        if variant.is_some()
            || field.index() >= 2
            || !shared_slice(&p.ty, false)
            || !self
                .adapter
                .shared_slice_pair(&self.body.locals.locals[id].ty, false)
        {
            return Err(unsupported("shared slice pair projection type/index"));
        }
        Ok(Some(E::Local {
            name: pair[field.index()].clone(),
        }))
    }
    pub(super) fn split_slice_call(&self, t: &u::Terminator) -> Result<Option<S>, String> {
        let u::TerminatorKind::Call { call, .. } = &t.kind else {
            return Ok(None);
        };
        let a::FnOperand::Regular(ptr) = &call.func else {
            return Ok(None);
        };
        let callee = &self.adapter.krate.fun_decls[self.adapter.resolve(ptr)?];
        if callee.item_meta.is_local
            || !matches!(callee.item_meta.name.name.last(), Some(a::PathElem::Ident(name, _)) if name == "split_at")
        {
            return Ok(None);
        }
        let path = &callee.item_meta.name.name;
        let identity = matches!(path.as_slice(), [a::PathElem::Ident(core, c), a::PathElem::Ident(slice, s), a::PathElem::Impl(a::ImplElem::Ty(receiver)), a::PathElem::Ident(method, m)]
            if core == "core" && slice == "slice" && method == "split_at"
                && c.is_zero() && s.is_zero() && m.is_zero()
                && matches!(receiver.skip_binder.kind(), a::TyKind::Slice(element, _) if variable(element)));
        if !identity
            || callee.item_meta.is_local
            || !matches!(callee.src, a::FunSource::Normal)
            || callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || callee.generics.regions.len() != 1
            || callee.generics.types.len() != 1
            || !callee.generics.const_generics.is_empty()
            || ptr.generics.regions.len() != 1
            || ptr.generics.types.len() != 1
            || !ptr.generics.const_generics.is_empty()
            || self.adapter.ty(&ptr.generics.types[0])? != Type::U8
            || !matches!(callee.signature.inputs.as_slice(), [slice, size] if shared_slice(slice, true) && self.adapter.ty(size).ok() == Some(Type::Usize))
            || !self
                .adapter
                .shared_slice_pair(&callee.signature.output, true)
            || !self.adapter.shared_slice_pair(&call.dest.ty, false)
            || !matches!(callee.signature.output.kind(), a::TyKind::Adt(r) if r.generics.types.iter().all(|output| output == &callee.signature.inputs[0]))
        {
            return Err(unsupported("split_at declaration/type mismatch"));
        }
        let [slice, midpoint] = call.args.as_slice() else {
            return Err(unsupported("split_at arity"));
        };
        if !shared_slice(slice.ty(), false) || self.adapter.ty(midpoint.ty())? != Type::Usize {
            return Err(unsupported("split_at argument types"));
        }
        let id = local(&call.dest)?;
        if !self
            .adapter
            .shared_slice_pair(&self.body.locals.locals[id].ty, false)
        {
            return Err(unsupported("split_at destination storage type"));
        }
        let [left, right] = self
            .slice_pairs
            .get(&id)
            .ok_or_else(|| unsupported("split_at destination storage"))?;
        Ok(Some(S::SliceSplit {
            slice: self.operand(slice)?,
            midpoint: self.operand(midpoint)?,
            left: left.clone(),
            right: right.clone(),
        }))
    }
}
