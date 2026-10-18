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
    /// one of a shape the importer does not take: generic, or with
    /// associated items or supertraits.
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
            || decl.generics.types.is_empty()
            || !decl.generics.const_generics.is_empty()
            || !decl.consts.is_empty()
            || !decl.types.is_empty()
            || !decl.implied_clauses.iter().all(marker)
        {
            return Err(unsupported(
                "crate trait with generics, associated items, or supertraits",
            ));
        }
        Ok(true)
    }

    /// The external function that stands for method `method` of crate trait
    /// `id` at the type arguments `generics` names after `Self`: the
    /// trait's path, its arguments, then the method, `traits::Shape::area` or
    /// `traits::Scale<i32>::scale`.
    pub(super) fn interface_name(
        &self,
        id: a::TraitDeclId,
        method: a::TraitMethodId,
        generics: &a::GenericArgs,
    ) -> Result<String, String> {
        let decl = &self.krate.trait_decls[id];
        let method = decl
            .methods
            .get(method)
            .ok_or_else(|| unsupported("missing trait method"))?;
        self.interface_name_at(
            id,
            &method.skip_binder.name.0,
            self.instance_arguments(generics)?,
        )
    }

    /// The interface function of method `method` of crate trait `id`'s
    /// instance at `arguments`, which the import then declares.
    fn interface_name_at(
        &self,
        id: a::TraitDeclId,
        method: &str,
        arguments: Vec<a::Ty>,
    ) -> Result<String, String> {
        let instance = self.trait_instance_name(id, &arguments)?;
        let mut name = instance.clone();
        super::super::names::push_path_segment(&mut name, method);
        self.trait_instances
            .borrow_mut()
            .entry(id)
            .or_default()
            .insert(instance, arguments);
        Ok(name)
    }

    /// The type arguments of a crate trait's instance, after `Self`. A
    /// generic trait is taken at scalar types.
    pub(super) fn instance_arguments(
        &self,
        generics: &a::GenericArgs,
    ) -> Result<Vec<a::Ty>, String> {
        let arguments = generics.types.iter().skip(1).cloned().collect::<Vec<_>>();
        for argument in &arguments {
            self.instance_argument_spelling(argument)?;
        }
        Ok(arguments)
    }

    /// The Rust spelling of a generic trait instance's type argument.
    fn instance_argument_spelling(&self, argument: &a::Ty) -> Result<&'static str, String> {
        let refused = || {
            unsupported(
                "crate trait instance at a type other than i32, u8, u16, u32, usize or bool",
            )
        };
        if matches!(argument.kind(), a::TyKind::TypeVar(_)) {
            return Err(refused());
        }
        Ok(match self.ty(argument).map_err(|_| refused())? {
            Type::I32 => "i32",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::Usize => "usize",
            Type::Bool => "bool",
            _ => return Err(refused()),
        })
    }

    /// The importer name of crate trait `id` at `arguments`: its path, then
    /// each argument, `traits::Scale<i32>`.
    pub(super) fn trait_instance_name(
        &self,
        id: a::TraitDeclId,
        arguments: &[a::Ty],
    ) -> Result<String, String> {
        let mut name = self.qualified_function_name(&self.krate.trait_decls[id].item_meta.name)?;
        for argument in arguments {
            super::super::names::push_type_argument(
                &mut name,
                self.instance_argument_spelling(argument)?,
            );
        }
        Ok(name)
    }

    /// The instances of crate trait `id` the crate uses: for a generic
    /// trait, those an implementation or a call names. A trait with no type
    /// parameter but `Self` has one instance.
    fn trait_instances(&self, id: a::TraitDeclId) -> Result<BTreeMap<String, Vec<a::Ty>>, String> {
        if self.krate.trait_decls[id].generics.types.len() == 1 {
            return Ok(BTreeMap::from([(
                self.trait_instance_name(id, &[])?,
                Vec::new(),
            )]));
        }
        Ok(self
            .trait_instances
            .borrow()
            .get(&id)
            .cloned()
            .unwrap_or_default())
    }

    /// `ty` in a method of a trait instance whose type arguments after
    /// `Self` are `arguments`.
    fn instance_ty(&self, ty: &a::Ty, arguments: &[a::Ty]) -> Result<Type, String> {
        if let a::TyKind::TypeVar(a::DeBruijnVar::Bound(_, var) | a::DeBruijnVar::Free(var)) =
            ty.kind()
            && let Some(argument) = var.index().checked_sub(1).and_then(|at| arguments.get(at))
        {
            return self.ty(argument);
        }
        self.ty(ty)
    }

    /// The interface function of each method of crate trait `id`. Its first
    /// parameter is the receiver, `&self` or `&mut self`; the rest, and its
    /// result, are scalars.
    pub(super) fn interface_functions(
        &self,
        id: a::TraitDeclId,
    ) -> Result<Vec<out::Function>, String> {
        let decl = &self.krate.trait_decls[id];
        let generic = decl.generics.types.len() > 1;
        let mut functions = Vec::new();
        for (instance, arguments) in self.trait_instances(id)? {
            for method in decl.methods.iter() {
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
                    let value_type = self.instance_ty(ty, &arguments)?;
                    if !closures::callable_scalar(&value_type) {
                        return Err(unsupported("trait method parameter other than a scalar"));
                    }
                    parameters.push(out::Place {
                        name: format!("__rust_arg_{}", index + 1),
                        value_type,
                        span: span(binder.item_meta.span),
                    });
                }
                let return_type = self.instance_ty(&signature.output, &arguments)?;
                if !closures::callable_scalar(&return_type) && return_type != Type::Unit {
                    return Err(unsupported("trait method result other than a scalar or ()"));
                }
                // A default method's body defines its interface function, as
                // the crate function the trait's default names.
                if binder.default.is_some() {
                    if generic {
                        return Err(unsupported("default method of a generic crate trait"));
                    }
                    continue;
                }
                let mut name = instance.clone();
                super::super::names::push_path_segment(&mut name, &binder.name.0);
                functions.push(out::Function {
                    name,
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
        let trait_name = self.trait_instance_name(
            trait_id,
            &self.instance_arguments(&imp.impl_trait.generics)?,
        )?;
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
            self.interface_name(trait_id, method, &imp.impl_trait.generics)?,
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
        self.interface_name(id, *method, &trait_ref.trait_decl_ref.skip_binder.generics)
            .map(Some)
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
        // The vtable's type is generic over the trait's arguments after
        // `Self`, which the reference's type gives it.
        let name = &self.krate.trait_decls[id].methods[*method]
            .skip_binder
            .name
            .0;
        self.interface_name_at(
            id,
            name,
            vtable_type.generics.types.iter().cloned().collect(),
        )
        .map(Some)
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

impl Adapter<'_> {
    /// The crate trait instance a type parameter is bound by, when it is
    /// one.
    fn type_parameter_interface(
        &self,
        generics: &a::GenericParams,
        parameter: a::TypeVarId,
    ) -> Option<(a::TraitDeclId, String)> {
        generics.trait_clauses.iter().find_map(|clause| {
            let trait_ref = &clause.trait_.skip_binder;
            let Some(a::TyKind::TypeVar(a::DeBruijnVar::Bound(_, id))) =
                trait_ref.generics.types.first().map(|ty| ty.kind())
            else {
                return None;
            };
            if *id != parameter || !matches!(self.interface_trait(trait_ref.id), Ok(true)) {
                return None;
            }
            self.trait_instance_at(trait_ref.id, &trait_ref.generics)
                .ok()
                .map(|instance| (trait_ref.id, instance))
        })
    }

    /// The importer name of crate trait `id`'s instance at the type arguments
    /// `generics` names after `Self`.
    fn trait_instance_at(
        &self,
        id: a::TraitDeclId,
        generics: &a::GenericArgs,
    ) -> Result<String, String> {
        self.trait_instance_name(id, &self.instance_arguments(generics)?)
    }

    /// The crate trait instance of a `dyn` predicate, when it is a crate
    /// trait's.
    pub(super) fn dyn_interface_instance(
        &self,
        predicate: &a::DynPredicate,
    ) -> Option<(a::TraitDeclId, String)> {
        let id = self.dyn_interface_trait(predicate).ok().flatten()?;
        let clause = predicate.binder.params.trait_clauses.iter().next()?;
        self.trait_instance_at(id, &clause.trait_.skip_binder.generics)
            .ok()
            .map(|instance| (id, instance))
    }

    /// The crate trait instance whose object a callee's parameter `ty` is,
    /// `&T` for `T: Trait` or `&dyn Trait`.
    pub(super) fn object_parameter_trait(
        &self,
        callee: &a::FunDecl,
        ty: &a::Ty,
    ) -> Option<(a::TraitDeclId, String)> {
        let a::TyKind::Ref(_, pointee, _) = ty.kind() else {
            return None;
        };
        match pointee.kind() {
            a::TyKind::TypeVar(a::DeBruijnVar::Bound(_, id)) => {
                self.type_parameter_interface(&callee.generics, *id)
            }
            a::TyKind::DynTrait(predicate) => self.dyn_interface_instance(predicate),
            _ => None,
        }
    }

    /// The external functions that turn a crate struct's memory into a crate
    /// trait's object and back, where a reference to the struct becomes the
    /// trait's object: `<S as Trait>::__pack` and `<S as Trait>::__unpack`.
    /// The sidecar's definitions of the trait's functions for the struct give
    /// them their contracts.
    pub(super) fn object_coercion_names(
        &self,
        record: a::TypeDeclId,
        trait_name: &str,
        shared: bool,
    ) -> Result<(String, String), String> {
        let record_name = &self.records[&record];
        let (pack, unpack) = if shared {
            (
                super::super::names::SHARED_PACK,
                super::super::names::SHARED_UNPACK,
            )
        } else {
            ("__pack", "__unpack")
        };
        Ok((
            super::super::names::trait_method_name(record_name, trait_name, pack),
            super::super::names::trait_method_name(record_name, trait_name, unpack),
        ))
    }

    /// The pack and unpack functions of `record` as the object of
    /// `trait_id`'s instance `instance`.
    pub(super) fn object_coercion_functions(
        &self,
        record: a::TypeDeclId,
        trait_id: a::TraitDeclId,
        instance: &str,
    ) -> Result<Vec<out::Function>, String> {
        let (pack, unpack) = self.object_coercion_names(record, instance, false)?;
        let (shared_pack, shared_unpack) = self.object_coercion_names(record, instance, true)?;
        let span = span(self.krate.trait_decls[trait_id].item_meta.span);
        Ok([pack, unpack, shared_pack, shared_unpack]
            .into_iter()
            .map(|name| out::Function {
                name,
                return_type: Type::Unit,
                parameters: vec![out::Place {
                    name: "__rust_arg_0".into(),
                    value_type: Type::Reference {
                        mutable: false,
                        pointee: Box::new(Type::Record {
                            name: self.records[&record].clone(),
                        }),
                    },
                    span: span.clone(),
                }],
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                span: span.clone(),
            })
            .collect())
    }
}

/// The locals of `body` a crate struct reference is unsized into a `&dyn`
/// crate trait for, with the struct, the trait and its instance, and whether
/// it is shared.
pub(super) fn unsized_objects(
    adapter: &Adapter<'_>,
    body: &u::ExprBody,
) -> BTreeMap<a::LocalId, (a::TypeDeclId, (a::TraitDeclId, String), bool)> {
    let mut objects = BTreeMap::new();
    for block in body.body.iter() {
        for statement in &block.statements {
            if let u::StatementKind::Assign(target, value) = &statement.kind
                && let a::PlaceKind::Local(local) = target.kind
                && let a::Rvalue::UnaryOp(
                    a::UnOp::Cast(a::CastKind::Unsize(
                        source,
                        destination,
                        a::UnsizingMetadata::VTable(..),
                    )),
                    _,
                ) = value
                && let a::TyKind::Ref(_, record, _) = source.kind()
                && let Ok(record) = adapter.record_id(record)
                && let a::TyKind::Ref(_, object, kind) = destination.kind()
                && let a::TyKind::DynTrait(predicate) = object.kind()
                && let Some(trait_id) = adapter.dyn_interface_instance(predicate)
            {
                objects.insert(
                    local,
                    (record, trait_id, matches!(kind, a::RefKind::Shared)),
                );
            }
        }
    }
    objects
}

/// Wraps each call that passes a crate struct reference as a crate trait's
/// object: before it, the struct's memory becomes the object, and after it,
/// the object becomes the memory again. Each wrapped call's block keeps its
/// statements and calls the first pack; new blocks call the rest, the call
/// itself, and the unpacks, then go where the call went.
pub(super) fn wrap_object_coercions(
    blocks: &mut Vec<out::MirBlock>,
    coercions: Vec<(usize, Vec<(String, String, E)>)>,
) -> Result<(), String> {
    for (block, wraps) in coercions {
        if wraps.is_empty() {
            continue;
        }
        let T::Call {
            target,
            destination,
            ..
        } = blocks[block].terminator.clone()
        else {
            return Err(unsupported("trait object coercion outside a call"));
        };
        let call = std::mem::replace(
            &mut blocks[block].terminator,
            T::Goto { target: usize::MAX },
        );
        let call_with = |function: &str, argument: &E, target: usize| T::Call {
            function: function.to_string(),
            arguments: vec![argument.clone()],
            owned_arguments: Vec::new(),
            destination: destination.clone(),
            target,
            through_pointer: false,
        };
        // Blocks in order: packs after the first, the call, the unpacks.
        let first = blocks.len();
        let packs = wraps.len() - 1;
        let call_block = first + packs;
        let first_unpack = call_block + 1;
        for (index, (pack, _, argument)) in wraps.iter().enumerate().skip(1) {
            let next = if index == wraps.len() - 1 {
                call_block
            } else {
                first + index
            };
            blocks.push(out::MirBlock {
                statements: Vec::new(),
                terminator: call_with(pack, argument, next),
            });
        }
        let mut call = call;
        if let T::Call {
            target: call_target,
            ..
        } = &mut call
        {
            *call_target = first_unpack;
        }
        blocks.push(out::MirBlock {
            statements: Vec::new(),
            terminator: call,
        });
        for (index, (_, unpack, argument)) in wraps.iter().enumerate() {
            let next = if index == wraps.len() - 1 {
                target
            } else {
                first_unpack + index + 1
            };
            blocks.push(out::MirBlock {
                statements: Vec::new(),
                terminator: call_with(unpack, argument, next),
            });
        }
        let (first_pack, _, argument) = &wraps[0];
        blocks[block].terminator = call_with(
            first_pack,
            argument,
            if packs == 0 { call_block } else { first },
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    const ARTIFACT: &[u8] = include_bytes!(
        "../../../../design/charon-trial/trait-methods/.click/trait_methods/shapes.rs.ullbc"
    );
    const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/trait-methods/shapes.rs");
    const INTERFACE: &str = "__rust_q_I13_trait_methods_I5_Shape_I4_area";

    fn decode_fixture(artifact: &ExtractionArtifact) -> Result<out::RustExport, String> {
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
        let artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
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

    const OBJECT_ARTIFACT: &[u8] = include_bytes!(
        "../../../../design/charon-trial/trait-objects/.click/trait_objects/shapes.rs.ullbc"
    );
    const OBJECT_SOURCE: &[u8] =
        include_bytes!("../../../../design/charon-trial/trait-objects/shapes.rs");

    // A crate struct reference passed for a bound type parameter's reference,
    // or unsized to `&dyn`, becomes the trait's object for the call: the call
    // is between the struct's pack and unpack, which the import declares.
    #[test]
    fn charon_trait_objects_wrap_coercions_in_pack_and_unpack() {
        let artifact: ExtractionArtifact = serde_json::from_slice(OBJECT_ARTIFACT).unwrap();
        let sources = [("shapes.rs".into(), OBJECT_SOURCE.to_vec())]
            .into_iter()
            .collect();
        let export = decode_crate(
            &serde_json::to_vec(&artifact).unwrap(),
            "shapes.rs",
            OBJECT_SOURCE,
            artifact.crate_config.as_ref(),
            Some(&sources),
        )
        .unwrap();
        let display = |name: &str| super::super::super::names::rust_display_name(name).unwrap();
        let function = |name: &str| export.functions.iter().find(|f| f.name == name).unwrap();
        // The calls in block order from the entry, following each call.
        let path = |name: &str| {
            let blocks = &function(name).mir.as_ref().unwrap().blocks;
            let mut block = 0;
            let mut calls = Vec::new();
            loop {
                match &blocks[block].terminator {
                    T::Call {
                        function, target, ..
                    } => {
                        calls.push(display(function));
                        block = *target;
                    }
                    T::Goto { target } => block = *target,
                    _ => break,
                }
            }
            calls
        };
        assert_eq!(
            path("__rust_q_I13_trait_objects_I13_through_bound"),
            [
                "<trait_objects::Square as trait_objects::Shape>::__pack_shared",
                "trait_objects::total",
                "<trait_objects::Square as trait_objects::Shape>::__unpack_shared",
            ]
        );
        assert_eq!(
            path("__rust_q_I13_trait_objects_I11_through_dyn"),
            [
                "<trait_objects::Circle as trait_objects::Shape>::__pack_shared",
                "trait_objects::dynamic",
                "<trait_objects::Circle as trait_objects::Shape>::__unpack_shared",
            ]
        );
        for name in [
            "<trait_objects::Square as trait_objects::Shape>::__pack",
            "<trait_objects::Circle as trait_objects::Shape>::__unpack",
            "<trait_objects::Square as trait_objects::Shape>::__pack_shared",
            "<trait_objects::Circle as trait_objects::Shape>::__unpack_shared",
        ] {
            let coercion = export
                .functions
                .iter()
                .find(|f| {
                    super::super::super::names::rust_display_name(&f.name).as_deref() == Some(name)
                })
                .unwrap();
            assert!(coercion.external && coercion.return_type == Type::Unit);
            assert!(super::super::super::names::is_object_coercion(
                &coercion.name
            ));
        }
    }

    // A generic crate trait has an interface function for each instance an
    // implementation or a call names, its signature at that instance's
    // arguments, and each is named with them.
    #[test]
    fn charon_generic_traits_import_an_interface_per_instance() {
        const GENERIC: &[u8] = include_bytes!(
            "../../../../design/charon-trial/generic-traits/.click/generic_traits/shapes.rs.ullbc"
        );
        const GENERIC_SOURCE: &[u8] =
            include_bytes!("../../../../design/charon-trial/generic-traits/shapes.rs");
        let artifact: ExtractionArtifact = serde_json::from_slice(GENERIC).unwrap();
        let sources = [("shapes.rs".into(), GENERIC_SOURCE.to_vec())]
            .into_iter()
            .collect();
        let export = decode_crate(
            &serde_json::to_vec(&artifact).unwrap(),
            "shapes.rs",
            GENERIC_SOURCE,
            artifact.crate_config.as_ref(),
            Some(&sources),
        )
        .unwrap();
        let display = |name: &str| super::super::super::names::rust_display_name(name).unwrap();
        let named = |path: &str| {
            export
                .functions
                .iter()
                .find(|f| {
                    super::super::super::names::rust_display_name(&f.name).as_deref() == Some(path)
                })
                .unwrap_or_else(|| panic!("{path}"))
        };
        for (interface, scalar) in [
            ("generic_traits::Scale<i32>::scale", Type::I32),
            ("generic_traits::Scale<u32>::scale", Type::U32),
        ] {
            let function = named(interface);
            assert!(function.external);
            assert_eq!(function.parameters[1].value_type, scalar);
            assert_eq!(function.return_type, scalar);
        }
        assert_eq!(
            named("<generic_traits::Square as generic_traits::Scale<i32>>::scale")
                .implements
                .as_deref()
                .map(display)
                .as_deref(),
            Some("generic_traits::Scale<i32>::scale")
        );
        for (caller, interface) in [
            ("generic_traits::total", "generic_traits::Scale<i32>::scale"),
            (
                "generic_traits::dynamic",
                "generic_traits::Scale<i32>::scale",
            ),
            (
                "generic_traits::wide_total",
                "generic_traits::Scale<u32>::scale",
            ),
        ] {
            assert_eq!(
                calls(named(caller))
                    .into_iter()
                    .map(display)
                    .collect::<Vec<_>>(),
                [interface]
            );
        }
        assert_eq!(
            super::super::super::names::interface_instance(
                &named("generic_traits::Scale<i32>::scale").name
            ),
            Some((
                super::super::super::names::qualified_name(["generic_traits", "Scale"]),
                vec!["i32".to_string()]
            ))
        );
    }

    // Every implementation a call through the trait can reach must be
    // imported to be checked, and a trait the importer does not read as an
    // interface is refused.
    #[test]
    fn charon_trait_methods_refuse_unread_traits_and_implementations() {
        for (mutation, expected) in [
            (1, "crate trait implementation method not imported"),
            (
                2,
                "crate trait with generics, associated items, or supertraits",
            ),
        ] {
            let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
            let krate = &mut artifact.data.translated;
            let shape = krate
                .trait_decls
                .iter()
                .find(|decl| decl.item_meta.is_local)
                .unwrap()
                .def_id;
            match mutation {
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
