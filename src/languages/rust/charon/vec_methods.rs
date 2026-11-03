//! Rust `Vec<T>` of a scalar: the value of the library's primitive type
//! `Vec<T>`. `Vec::new()`, `Vec::with_capacity(n)`, `v.push(x)`, `v.len()`
//! and `v[i]` each call an external function the importer declares once per
//! method and element type, whose contract states the call with the
//! library's `vec::len`, `vec::get` and `vec::push`.
//!
//! The compiler reads `v[i]` through a reference, `r = <Vec<T> as
//! Index<usize>>::index(&v, i); x = copy *r`. A vector's elements are
//! values of the model, not memory, so the importer reads the element
//! itself: `r` holds the element, and each `*r` reads `r`
//! (`vec_index_body`).
use super::*;

/// The `Vec` methods the library specifies.
const METHODS: &[&str] = &["new", "with_capacity", "push", "len", "index"];

impl Adapter<'_> {
    /// The `Vec` method a call of `callee` is, when it is one the library
    /// specifies: an inherent method of `alloc::vec::Vec`, or `index` of its
    /// `core::ops::Index` implementation.
    fn vec_method(&self, callee: &a::FunDecl) -> Option<&'static str> {
        if callee.item_meta.is_local {
            return None;
        }
        let [
            a::PathElem::Ident(alloc, _),
            a::PathElem::Ident(vec, _),
            a::PathElem::Impl(implementation),
            a::PathElem::Ident(method, d),
        ] = callee.item_meta.name.name.as_slice()
        else {
            return None;
        };
        if alloc != "alloc" || vec != "vec" || *d != a::Disambiguator::ZERO {
            return None;
        }
        let method = *METHODS.iter().find(|known| **known == method)?;
        match (implementation, &callee.src) {
            (a::ImplElem::Ty(receiver), a::FunSource::Normal) => (method != "index"
                && self.vec_element(&receiver.skip_binder).is_some())
            .then_some(method),
            (_, a::FunSource::TraitImpl { trait_ref, .. }) if method == "index" => {
                let index = &self.krate.trait_decls[trait_ref.id];
                (!index.item_meta.is_local
                    && protocol::path(&index.item_meta.name, &["core", "ops", "index", "Index"]))
                .then_some(method)
            }
            _ => None,
        }
    }

    /// The external function a call of `callee` calls when it is a `Vec`
    /// method the library specifies, declared once per method and element
    /// type.
    pub(super) fn vec_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let Some(method) = self.vec_method(callee) else {
            return Ok(None);
        };
        let refused = || unsupported(&format!("`Vec::{method}` signature"));
        if callee.signature.is_unsafe
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.const_generics.is_empty()
        {
            return Err(refused());
        }
        let arguments = call
            .args
            .iter()
            .map(|argument| self.ty(argument.ty()))
            .collect::<Result<Vec<_>, _>>()?;
        let destination = self.ty(&call.dest.ty)?;
        let vector = |reference: &Type, mutable: bool| match reference {
            Type::Reference {
                mutable: written,
                pointee,
            } if *written == mutable => match pointee.as_ref() {
                Type::Vec { element } => Some((**element).clone()),
                _ => None,
            },
            _ => None,
        };
        // Each method's element type, parameters and result.
        let (element, parameters, return_type) = match (method, arguments.as_slice()) {
            ("new", []) => {
                let Type::Vec { element } = &destination else {
                    return Err(refused());
                };
                ((**element).clone(), vec![], destination.clone())
            }
            ("with_capacity", [Type::Usize]) => {
                let Type::Vec { element } = &destination else {
                    return Err(refused());
                };
                (
                    (**element).clone(),
                    vec![("capacity", Type::Usize)],
                    destination.clone(),
                )
            }
            ("push", [receiver, value]) => {
                let element = vector(receiver, true).ok_or_else(refused)?;
                if *value != element || destination != Type::Unit {
                    return Err(refused());
                }
                (
                    element.clone(),
                    vec![("v", receiver.clone()), ("x", element)],
                    Type::Unit,
                )
            }
            ("len", [receiver]) => {
                let element = vector(receiver, false).ok_or_else(refused)?;
                if destination != Type::Usize {
                    return Err(refused());
                }
                (element, vec![("v", receiver.clone())], Type::Usize)
            }
            // `vec_index_body` gave the result the element's type.
            ("index", [receiver, Type::Usize]) => {
                let element = vector(receiver, false).ok_or_else(refused)?;
                if destination != element {
                    return Err(refused());
                }
                (
                    element.clone(),
                    vec![("v", receiver.clone()), ("i", Type::Usize)],
                    element,
                )
            }
            _ => return Err(refused()),
        };
        let element_name = element.scalar_name().ok_or_else(refused)?;
        let mut function = super::super::names::qualified_name(["Vec", method]);
        super::super::names::push_type_argument(&mut function, element_name);
        let parameters = parameters
            .into_iter()
            .map(|(name, value_type)| out::Place {
                name: name.into(),
                value_type,
                span: span(callee.item_meta.span),
            })
            .collect();
        self.core_methods.borrow_mut().insert(
            function.clone(),
            out::Function {
                name: function.clone(),
                return_type,
                parameters,
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(format!("{}{method}", super::super::standard_library::VEC)),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(function))
    }

    /// `body` with the result of each `v[i]` read as the element itself, or
    /// `None` when it indexes no vector.
    ///
    /// The call's destination, a `&T`, becomes a `T`, and each `*r` reads
    /// `r`. Only a destination the body reads through and nothing else is
    /// rewritten: the compiler's `x = copy *r`, or `*r` as an operand.
    /// Anything else, a reference kept or passed on, is refused.
    pub(super) fn vec_index_body(&self, body: &u::ExprBody) -> Result<Option<u::ExprBody>, String> {
        let mut results = Vec::new();
        for block in &body.body {
            let u::TerminatorKind::Call { call, .. } = &block.terminator.kind else {
                continue;
            };
            let a::FnOperand::Regular(pointer) = &call.func else {
                continue;
            };
            let Ok(callee) = self.resolve(pointer) else {
                continue;
            };
            let Some(callee) = self.krate.fun_decls.get(callee) else {
                continue;
            };
            if self.vec_method(callee) != Some("index") {
                continue;
            }
            let (Some(result), a::TyKind::Ref(_, element, a::RefKind::Shared)) =
                (call.dest.as_local(), call.dest.ty.kind())
            else {
                return Err(unsupported("`Vec` index result"));
            };
            results.push((result, element.clone()));
        }
        if results.is_empty() {
            return Ok(None);
        }
        let mut body = body.clone();
        for (result, element) in results {
            // Every mention of the result other than the call's destination
            // and its storage markers is a read through it.
            let mut mentions = 0;
            let mut reads = 0;
            for block in &body.body {
                block.dyn_visit(|local: &a::LocalId| {
                    if *local == result {
                        mentions += 1;
                    }
                });
                block.dyn_visit(|place: &a::Place| {
                    if matches!(&place.kind, a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                        if base.as_local() == Some(result))
                    {
                        reads += 1;
                    }
                });
                for statement in &block.statements {
                    if matches!(statement.kind,
                        u::StatementKind::StorageLive(local) | u::StatementKind::StorageDead(local)
                            if local == result)
                    {
                        reads += 1;
                    }
                }
            }
            if mentions != reads + 1 {
                return Err(unsupported(
                    "`Vec` index result used other than to read the element",
                ));
            }
            body.locals.locals[result].ty = element.clone();
            for block in body.body.iter_mut() {
                block.dyn_visit_mut(|place: &mut a::Place| {
                    let through = matches!(&place.kind,
                        a::PlaceKind::Projection(base, a::ProjectionElem::Deref)
                            if base.as_local() == Some(result));
                    if through || place.as_local() == Some(result) {
                        *place = a::Place::new(result, element.clone());
                    }
                });
            }
        }
        Ok(Some(body))
    }
}
