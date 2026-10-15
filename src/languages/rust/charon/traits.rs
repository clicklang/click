//! Crate traits as method interfaces. A method of a crate trait, `trait
//! Shape { fn area(&self, scale: i32) -> i32; }`, is imported as an external
//! function, `traits::Shape::area`, whose contract the sidecar's `trait`
//! block states. A call through a trait bound, `s.area(x)` for `s: &T` and
//! `T: Shape`, or through a `&dyn Shape`'s vtable, is a call of that
//! function. Each implementation, `<traits::Square as traits::Shape>::area`,
//! is an ordinary function of the crate, marked as implementing the
//! interface; the sidecar's checks that its contract refines the interface's.
//!
//! The receiver is a reference to a value of a type the caller does not
//! know, so the interface's contract reads nothing through it. Every
//! implementation a call can reach is in the import: a generic call names
//! the implementation it instantiates, and an unsizing to `dyn` names its
//! vtable, so Charon translates every implementation used.
use super::*;

impl Adapter<'_> {
    /// Whether `id` is a crate trait whose methods are interfaces, refusing
    /// one of a shape the importer does not take: generic, with associated
    /// items or supertraits, or with a default method.
    pub(super) fn interface_trait(&self, id: a::TraitDeclId) -> Result<bool, String> {
        let Some(decl) = self.krate.trait_decls.get(id) else {
            return Err(unsupported("missing trait"));
        };
        if !decl.item_meta.is_local || decl.item_meta.lang_item.is_some() {
            return Ok(false);
        }
        if !self.crate_mode {
            return Err(unsupported("crate trait outside crate imports"));
        }
        let marker = |clause: &a::TraitParam| {
            self.krate
                .trait_decls
                .get(clause.trait_.skip_binder.id)
                .is_some_and(|decl| {
                    matches!(
                        decl.item_meta.lang_item,
                        Some(LangItem::MetaSized | LangItem::Sized | LangItem::Destruct)
                    )
                })
        };
        if decl.is_unsafe
            || !matches!(decl.src, a::TraitDeclSource::Normal)
            || decl.generics.types.len() != 1
            || !decl.generics.const_generics.is_empty()
            || !decl.consts.is_empty()
            || !decl.types.is_empty()
            || !decl.implied_clauses.iter().all(marker)
        {
            return Err(unsupported(
                "crate trait with generics, associated items, or supertraits",
            ));
        }
        if decl
            .methods
            .iter()
            .any(|method| method.skip_binder.default.is_some())
        {
            return Err(unsupported("crate trait method with a default body"));
        }
        Ok(true)
    }

    /// The external function that stands for method `method` of crate trait
    /// `id`: the trait's path, then the method, `traits::Shape::area`.
    pub(super) fn interface_name(
        &self,
        id: a::TraitDeclId,
        method: a::TraitMethodId,
    ) -> Result<String, String> {
        let decl = &self.krate.trait_decls[id];
        let method = decl
            .methods
            .get(method)
            .ok_or_else(|| unsupported("missing trait method"))?;
        let mut name = self.qualified_function_name(&decl.item_meta.name)?;
        super::super::names::push_path_segment(&mut name, &method.skip_binder.name.0);
        Ok(name)
    }

    /// The interface function of each method of crate trait `id`. Its first
    /// parameter is the receiver, `&self` or `&mut self`; the rest, and its
    /// result, are scalars.
    pub(super) fn interface_functions(
        &self,
        id: a::TraitDeclId,
    ) -> Result<Vec<out::Function>, String> {
        let decl = &self.krate.trait_decls[id];
        let mut functions = Vec::new();
        for (method_id, method) in decl.methods.iter_indexed() {
            let binder = &method.skip_binder;
            let signature = &binder.signature;
            if !method.params.types.is_empty()
                || !method.params.const_generics.is_empty()
                || signature.is_unsafe
                || signature.is_variadic
                || signature.abi != a::Abi::Rust
            {
                return Err(unsupported("generic, unsafe, or foreign trait method"));
            }
            let Some((receiver, inputs)) = signature.inputs.split_first() else {
                return Err(unsupported("trait method without a receiver"));
            };
            let a::TyKind::Ref(_, pointee, kind) = receiver.kind() else {
                return Err(unsupported(
                    "trait method receiver other than `&self` or `&mut self`",
                ));
            };
            if !matches!(pointee.kind(), a::TyKind::TypeVar(a::DeBruijnVar::Bound(_, id)) if id.index() == 0)
            {
                return Err(unsupported(
                    "trait method receiver other than `&self` or `&mut self`",
                ));
            }
            let mut parameters = vec![out::Place {
                name: "__rust_arg_0".into(),
                value_type: Type::Reference {
                    mutable: *kind == a::RefKind::Mut,
                    pointee: Box::new(Type::TraitObject),
                },
                span: span(binder.item_meta.span),
            }];
            for (index, ty) in inputs.iter().enumerate() {
                let value_type = self.ty(ty)?;
                if !closures::callable_scalar(&value_type) {
                    return Err(unsupported("trait method parameter other than a scalar"));
                }
                parameters.push(out::Place {
                    name: format!("__rust_arg_{}", index + 1),
                    value_type,
                    span: span(binder.item_meta.span),
                });
            }
            let return_type = self.ty(&signature.output)?;
            if !closures::callable_scalar(&return_type) && return_type != Type::Unit {
                return Err(unsupported("trait method result other than a scalar or ()"));
            }
            functions.push(out::Function {
                name: self.interface_name(id, method_id)?,
                return_type,
                parameters,
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                span: span(binder.item_meta.span),
            });
        }
        Ok(functions)
    }

    /// The trait of a `dyn Trait` that is a crate trait's interface.
    pub(super) fn dyn_interface_trait(
        &self,
        predicate: &a::DynPredicate,
    ) -> Result<Option<a::TraitDeclId>, String> {
        let clauses = predicate
            .binder
            .params
            .trait_clauses
            .iter()
            .collect::<Vec<_>>();
        let [clause] = clauses.as_slice() else {
            return Ok(None);
        };
        let id = clause.trait_.skip_binder.id;
        Ok(self.interface_trait(id)?.then_some(id))
    }

    /// The name of a crate trait method's implementation, `<traits::Square
    /// as traits::Shape>::area`, and the interface function it implements.
    pub(super) fn trait_impl_method(
        &self,
        f: &a::FunDecl,
        impl_id: a::TraitImplId,
        trait_id: a::TraitDeclId,
        method: a::TraitMethodId,
    ) -> Result<(String, String), String> {
        let imp = self
            .krate
            .trait_impls
            .get(impl_id)
            .ok_or_else(|| unsupported("missing trait implementation"))?;
        // The trait has no default methods, so each method is the impl's own.
        if imp.is_unsafe
            || !imp.generics.types.is_empty()
            || !imp.generics.const_generics.is_empty()
            || !f.generics.types.is_empty()
        {
            return Err(unsupported("generic crate trait implementation"));
        }
        let receiver = imp
            .impl_trait
            .generics
            .types
            .first()
            .ok_or_else(|| unsupported("trait implementation without a type"))?;
        let record = self.record_id(receiver).map_err(|_| {
            unsupported("crate trait implemented for a type other than a crate struct")
        })?;
        let trait_name =
            self.qualified_function_name(&self.krate.trait_decls[trait_id].item_meta.name)?;
        let method_name = &self.krate.trait_decls[trait_id].methods[method]
            .skip_binder
            .name
            .0;
        Ok((
            super::super::names::trait_method_name(
                &self.records[&record],
                &trait_name,
                method_name,
            ),
            self.interface_name(trait_id, method)?,
        ))
    }

    /// The interface function a call through a trait bound names, `s.area(x)`
    /// for `T: Shape`; `None` for any other call.
    pub(super) fn interface_call(&self, pointer: &a::FnPtr) -> Result<Option<String>, String> {
        let a::FnPtrKind::Trait(trait_ref, method) = pointer.kind.as_ref() else {
            return Ok(None);
        };
        if matches!(trait_ref.kind, a::TraitRefKind::TraitImpl(_)) {
            return Ok(None);
        }
        let id = trait_ref.trait_decl_ref.skip_binder.id;
        if !self.interface_trait(id)? {
            return Ok(None);
        }
        if !pointer.generics.types.is_empty() || !pointer.generics.const_generics.is_empty() {
            return Err(unsupported("generic trait method call"));
        }
        self.interface_name(id, *method).map(Some)
    }

    /// The interface function a call through a `dyn` vtable's method field
    /// names, `(*s.metadata).method_area`; `None` for any other pointer.
    pub(super) fn vtable_call(&self, pointer: &a::Operand) -> Result<Option<String>, String> {
        let (a::Operand::Copy(place) | a::Operand::Move(place)) = pointer else {
            return Ok(None);
        };
        let a::PlaceKind::Projection(vtable, a::ProjectionElem::Field(None, field)) = &place.kind
        else {
            return Ok(None);
        };
        let a::TyKind::Adt(vtable_type) = vtable.ty.kind() else {
            return Ok(None);
        };
        let Some(a::TypeSource::VTable {
            dyn_predicate,
            field_map,
            ..
        }) = self
            .krate
            .type_decls
            .get(vtable_type.id)
            .map(|decl| &decl.src)
        else {
            return Ok(None);
        };
        let a::PlaceKind::Projection(metadata, a::ProjectionElem::Deref) = &vtable.kind else {
            return Err(unsupported("vtable read other than a reference's metadata"));
        };
        if !matches!(
            &metadata.kind,
            a::PlaceKind::Projection(_, a::ProjectionElem::PtrMetadata)
        ) {
            return Err(unsupported("vtable read other than a reference's metadata"));
        }
        let Some(a::VTableField::Method(method)) = field_map.get(*field) else {
            return Err(unsupported(
                "call through a vtable field other than a method",
            ));
        };
        let Some(id) = self.dyn_interface_trait(dyn_predicate)? else {
            return Err(unsupported(
                "call through a vtable of a trait other than a crate trait",
            ));
        };
        self.interface_name(id, *method).map(Some)
    }
}

impl BodyAdapter<'_, '_> {
    /// A call of the interface function `function`: the receiver, a reference
    /// to a value of unknown type, then the method's scalar arguments.
    pub(super) fn interface_method_call(
        &self,
        function: String,
        call: &a::Call,
        target: u::BlockId,
    ) -> Result<T, String> {
        let a::PlaceKind::Local(dest) = call.dest.kind else {
            return Err(unsupported("projected call destination"));
        };
        let Some((receiver, _)) = call.args.split_first() else {
            return Err(unsupported("trait method call without a receiver"));
        };
        if call.safety == a::CallSafety::Unsafe
            || !matches!(self.adapter.ty(receiver.ty())?, Type::Reference { pointee, .. } if *pointee == Type::TraitObject)
        {
            return Err(unsupported("trait method call receiver"));
        }
        let arguments = call
            .args
            .iter()
            .map(|argument| self.operand(argument))
            .collect::<Result<_, String>>()?;
        Ok(T::Call {
            function,
            arguments,
            owned_arguments: Vec::new(),
            destination: self.local(dest)?,
            target: target.index(),
            through_pointer: false,
        })
    }

    /// `&*s` for a reference `s` to a value of unknown type, with or without
    /// a `dyn` vtable: the same reference. `None` for any other borrow.
    pub(super) fn trait_object_reborrow(&self, place: &a::Place) -> Result<Option<E>, String> {
        let a::PlaceKind::Projection(base, a::ProjectionElem::Deref) = &place.kind else {
            return Ok(None);
        };
        if !matches!(self.adapter.ty(&base.ty), Ok(Type::Reference { pointee, .. }) if *pointee == Type::TraitObject)
        {
            return Ok(None);
        }
        self.place(base).map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ARTIFACT: &[u8] =
        include_bytes!("../../../../design/charon-trial/trait-methods/shapes.ullbc");
    const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/trait-methods/shapes.rs");
    const INTERFACE: &str = "__rust_q_I13_trait_methods_I5_Shape_I4_area";

    fn decode_fixture(artifact: &TrialArtifact) -> Result<out::RustExport, String> {
        let sources = [("shapes.rs".into(), SOURCE.to_vec())]
            .into_iter()
            .collect();
        decode_crate(
            &serde_json::to_vec(artifact).unwrap(),
            "shapes.rs",
            SOURCE,
            artifact.crate_config.as_ref(),
            Some(&sources),
        )
    }

    fn calls(function: &out::Function) -> Vec<&str> {
        function
            .mir
            .iter()
            .flat_map(|mir| &mir.blocks)
            .filter_map(|block| match &block.terminator {
                T::Call { function, .. } => Some(function.as_str()),
                _ => None,
            })
            .collect()
    }

    // A trait method is an external interface function whose receiver is a
    // reference to a value of unknown type; each implementation names it,
    // and a call through a bound or a `dyn` vtable calls it.
    #[test]
    fn charon_trait_methods_import_interfaces_and_dispatch() {
        let artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let export = decode_fixture(&artifact).unwrap();
        let function = |name: &str| export.functions.iter().find(|f| f.name == name).unwrap();
        let interface = function(INTERFACE);
        assert!(interface.external && interface.mir.is_none());
        assert_eq!(
            interface.parameters[0].value_type,
            Type::Reference {
                mutable: false,
                pointee: Box::new(Type::TraitObject)
            }
        );
        let implementations = export
            .functions
            .iter()
            .filter(|f| f.implements.as_deref() == Some(INTERFACE))
            .map(|f| super::super::super::names::rust_display_name(&f.name).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            implementations,
            [
                "<trait_methods::Square as trait_methods::Shape>::area",
                "<trait_methods::Circle as trait_methods::Shape>::area"
            ]
        );
        for caller in [
            "__rust_q_I13_trait_methods_I5_total",
            "__rust_q_I13_trait_methods_I7_dynamic",
        ] {
            assert_eq!(calls(function(caller)), [INTERFACE]);
        }
        // A call on a known type is a call of its implementation.
        let direct = calls(function("__rust_q_I13_trait_methods_I6_direct"));
        assert_eq!(direct.len(), 1);
        assert_ne!(direct[0], INTERFACE);
    }

    // Every implementation a call through the trait can reach must be
    // imported to be checked, and a trait the importer does not read as an
    // interface is refused.
    #[test]
    fn charon_trait_methods_refuse_unread_traits_and_implementations() {
        for (mutation, expected) in [
            (0, "crate trait method with a default body"),
            (1, "crate trait implementation method not imported"),
            (
                2,
                "crate trait with generics, associated items, or supertraits",
            ),
        ] {
            let mut artifact: TrialArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let krate = &mut artifact.data.translated;
            let shape = krate
                .trait_decls
                .iter()
                .find(|decl| decl.item_meta.is_local)
                .unwrap()
                .def_id;
            match mutation {
                0 => {
                    let default = krate
                        .fun_decls
                        .iter()
                        .find(|f| {
                            matches!(&f.src, a::FunSource::TraitImpl { trait_ref, .. } if trait_ref.id == shape)
                        })
                        .unwrap()
                        .def_id;
                    for method in krate.trait_decls[shape].methods.iter_mut() {
                        method.skip_binder.default = Some(a::FunDeclRef {
                            id: default,
                            generics: Box::new(a::GenericArgs::empty()),
                        });
                    }
                }
                1 => {
                    // `Circle`'s, which only a call through the trait reaches.
                    let circle = krate
                        .trait_impls
                        .iter()
                        .find(|imp| {
                            matches!(imp.impl_trait.generics.types[0].kind(), a::TyKind::Adt(r)
                                if format!("{:?}", krate.type_decls[r.id].item_meta.name).contains("Circle"))
                        })
                        .unwrap()
                        .methods
                        .iter()
                        .next()
                        .unwrap()
                        .skip_binder
                        .id;
                    krate.fun_decls[circle].item_meta.is_local = false;
                }
                _ => {
                    let marker =
                        krate.trait_decls[shape].implied_clauses[a::TraitClauseId::new(0)].clone();
                    let mut supertrait = marker;
                    supertrait.trait_.skip_binder.id = shape;
                    krate.trait_decls[shape].implied_clauses.push(supertrait);
                }
            }
            let error = decode_fixture(&artifact).unwrap_err();
            assert!(error.contains(expected), "{mutation}: {error}");
        }
    }
}
