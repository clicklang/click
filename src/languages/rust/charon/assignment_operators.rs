//! Resolved source assignment operators execute their imported bodies.
//! Their trait names authorize dispatch, never arithmetic shortcuts.
use super::*;

fn rhs_name(ty: &Type) -> Result<String, String> {
    Ok(match ty {
        Type::I32 => "i32".into(),
        Type::U8 => "u8".into(),
        Type::U16 => "u16".into(),
        Type::U32 => "u32".into(),
        Type::Usize => "usize".into(),
        Type::Bool => "bool".into(),
        Type::Record { name } => format!("value_{}{name}", name.len()),
        Type::Reference { mutable, pointee } => {
            let name = match pointee.as_ref() {
                Type::Record { name } => name.clone(),
                Type::I32 | Type::U8 | Type::U16 | Type::U32 => rhs_name(pointee)?,
                _ => return Err(unsupported("assignment operator reference operand")),
            };
            format!("ref_{}{name}", if *mutable { "mut_" } else { "" })
        }
        _ => {
            return Err(unsupported(
                "assignment operator operand (by-value aggregates remain later work)",
            ));
        }
    })
}
fn trait_variable(ty: &a::Ty, index: usize) -> bool {
    matches!(ty.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(depth, id)) if depth.index == 1 && id.index() == index)
}
impl Adapter<'_> {
    pub(super) fn assignment_operator_name(&self, f: &a::FunDecl) -> Result<String, String> {
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &f.src
        else {
            return Err(unsupported("assignment operator source"));
        };
        let tr = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing operator trait"))?;
        let imp = self
            .krate
            .trait_impls
            .get(impl_ref.id)
            .ok_or_else(|| unsupported("missing operator implementation"))?;
        let (trait_name, method_name) = match tr.item_meta.lang_item {
            Some(LangItem::AddAssign) => ("AddAssign", "add_assign"),
            Some(LangItem::MulAssign) => ("MulAssign", "mul_assign"),
            Some(LangItem::RemAssign) => ("RemAssign", "rem_assign"),
            _ => {
                return Err(unsupported(
                    "source trait method outside Drop and assignment operators",
                ));
            }
        };
        let method = tr
            .methods
            .get(*item_id)
            .ok_or_else(|| unsupported("missing operator method"))?;
        if tr.item_meta.is_local
            || tr.is_unsafe
            || !matches!(tr.src, a::TraitDeclSource::Normal)
            || !protocol::path(&tr.item_meta.name, &["core", "ops", "arith", trait_name])
            || tr.generics.types.len() != 2
            || !tr.generics.const_generics.is_empty()
            || !tr.generics.regions.is_empty()
            || tr.methods.iter().take(2).count() != 1
            || item_id.index() != 0
            || method.skip_binder.name.0 != method_name
            || !matches!(method.skip_binder.signature.inputs.as_slice(), [receiver, rhs] if matches!(receiver.kind(), a::TyKind::Ref(_, self_ty, a::RefKind::Mut) if trait_variable(self_ty, 0)) && trait_variable(rhs, 1))
            || !method.skip_binder.signature.output.is_unit()
            || method.skip_binder.signature.is_unsafe
            || method.skip_binder.signature.is_variadic
            || method.skip_binder.signature.abi != a::Abi::Rust
            || !imp.item_meta.is_local
            || imp.is_unsafe
            || imp.is_negative
            || !matches!(imp.src, a::TraitImplSource::Normal)
            || imp.impl_trait.id != trait_ref.id
            || imp.impl_trait.generics.types.len() != 2
            || !imp.impl_trait.generics.const_generics.is_empty()
            || !imp.generics.types.is_empty()
            || !imp.generics.const_generics.is_empty()
            || imp.methods.iter().take(2).count() != 1
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
            || (!self.crate_mode && f.item_meta.name.name.len() != 3)
            || !local_impl_method_path(
                &f.item_meta.name,
                &self.krate.crate_name,
                impl_ref.id,
                method_name,
            )
            || f.item_meta.name.name[..f.item_meta.name.name.len() - 1] != imp.item_meta.name.name
            || !f.signature.output.is_unit()
        {
            return Err(unsupported(
                "assignment operator declaration/implementation identity",
            ));
        }
        let self_ty = &imp.impl_trait.generics.types[0];
        let record = self.record_id(self_ty)?;
        let rhs = self.ty(&imp.impl_trait.generics.types[1])?;
        let [receiver, argument] = f.signature.inputs.as_slice() else {
            return Err(unsupported("assignment operator arity"));
        };
        if !matches!(receiver.kind(), a::TyKind::Ref(_, p, a::RefKind::Mut) if self.record_id(p).ok() == Some(record))
            || self.ty(argument)? != rhs
            || trait_ref.generics.types.len() != 2
            || self.ty(&trait_ref.generics.types[0])? != self.ty(self_ty)?
            || self.ty(&trait_ref.generics.types[1])? != rhs
        {
            return Err(unsupported(
                "assignment operator receiver/operand signature",
            ));
        }
        Ok(format!(
            "{}_{}_{}",
            self.records[&record],
            method_name,
            rhs_name(&rhs)?
        ))
    }
    pub(super) fn assignment_operator_call(
        &self,
        callee: &a::FunDecl,
        ptr: &a::FnPtr,
        call: &a::Call,
    ) -> Result<(), String> {
        let a::FunSource::TraitImpl {
            trait_ref,
            impl_ref,
            item_id,
            ..
        } = &callee.src
        else {
            return Ok(());
        };
        let tr = self
            .krate
            .trait_decls
            .get(trait_ref.id)
            .ok_or_else(|| unsupported("missing call trait"))?;
        if !matches!(
            tr.item_meta.lang_item,
            Some(LangItem::AddAssign | LangItem::MulAssign | LangItem::RemAssign)
        ) {
            return Ok(());
        }
        self.assignment_operator_name(callee)?;
        if call.safety == a::CallSafety::Unsafe
            || !ptr.generics.types.is_empty()
            || !ptr.generics.const_generics.is_empty()
            || ptr.generics.regions.len() != callee.generics.regions.len()
            || call.args.len() != callee.signature.inputs.len()
            || self.ty(&call.dest.ty)? != Type::Unit
        {
            return Err(unsupported("assignment operator call signature"));
        }
        for (arg, parameter) in call.args.iter().zip(&callee.signature.inputs) {
            if self.ty(arg.ty())? != self.ty(parameter)? {
                return Err(unsupported("assignment operator call operand type"));
            }
        }
        if let a::FnPtrKind::Trait(reference, method) = ptr.kind.as_ref()
            && (*method != *item_id
                || reference.trait_decl_ref.skip_binder.id != trait_ref.id
                || !matches!(&reference.kind, a::TraitRefKind::TraitImpl(r) if r.id == impl_ref.id))
        {
            return Err(unsupported("assignment operator resolved trait dispatch"));
        }
        Ok(())
    }
}
