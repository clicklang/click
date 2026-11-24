//! Rust `str` methods, `s.len()` and `s.is_empty()`: each call is a call of
//! an external function the importer declares once per method, whose
//! contract is the library's (`library/rust/str.interface.click`). A
//! `&str` is read as a shared slice of its bytes ([`Adapter::ty`]), so the
//! contracts state the methods over the slice's length. The callee is
//! checked by identity, an inherent method of `core::str`, with the
//! signature the method has.
use super::*;

impl Adapter<'_> {
    /// The external function a call of `callee` calls when it is a `str`
    /// method the library specifies, declared once per method.
    pub(super) fn str_method_call(
        &self,
        callee: &a::FunDecl,
        pointer: &a::FnPtr,
        call: &a::Call,
    ) -> Result<Option<String>, String> {
        let name = &callee.item_meta.name.name;
        let method = match name.as_slice() {
            [
                a::PathElem::Ident(core, _),
                a::PathElem::Ident(module, _),
                a::PathElem::Impl(a::ImplElem::Ty(_)),
                a::PathElem::Ident(method, d),
            ] if !callee.item_meta.is_local
                && matches!(callee.src, a::FunSource::Normal)
                && core == "core"
                && module == "str"
                && *d == a::Disambiguator::ZERO =>
            {
                method.as_str()
            }
            _ => return Ok(None),
        };
        let Some(result) = super::super::standard_library::str_method_result(method) else {
            return Ok(None);
        };
        let shared = Type::ByteSlice { mutable: false };
        if callee.signature.is_unsafe
            || callee.signature.is_variadic
            || callee.signature.abi != a::Abi::Rust
            || call.safety == a::CallSafety::Unsafe
            || !pointer.generics.types.is_empty()
            || !pointer.generics.const_generics.is_empty()
            || call.args.len() != 1
            || callee.signature.inputs.len() != 1
            || self.ty(call.args[0].ty())? != shared
            || self.ty(&call.dest.ty)? != result
        {
            return Err(unsupported(&format!(
                "core method `str::{method}` signature"
            )));
        }
        let name = super::super::names::qualified_name(["str", method]);
        self.core_methods.borrow_mut().insert(
            name.clone(),
            out::Function {
                sites: Vec::new(),
                name: name.clone(),
                return_type: result,
                parameters: vec![out::Place {
                    name: "s".into(),
                    value_type: shared,
                    span: span(callee.item_meta.span),
                }],
                body: vec![],
                mir: None,
                external: true,
                captures: 0,
                implements: None,
                instance_of: None,
                core_method: Some(name.clone()),
                span: span(callee.item_meta.span),
            },
        );
        Ok(Some(name))
    }
}
