//! The scope a proof clause is written in, read from declarations alone: the
//! Click names the proof binds, at the types they were bound with, and the C
//! names in scope at the clause's position, at their declared types. Unlike a
//! lowering context, it holds no C value, so a proof driver can elaborate a
//! clause against it before lowering (`design/typed-surface.md`).

use super::*;
use declarations::Declarations;
use typing_environment::{PointInputs, TypeScope};

#[derive(Clone, Copy)]
pub(super) struct DeclaredScope<'a> {
    pub(super) declarations: &'a Declarations<'a>,
    pub(super) integer_values: &'a PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    pub(super) algebraic_values: &'a PersistentBinderMap<SpecAlgebraicExpression>,
    /// Whether bare `result` names the function's return value here.
    pub(super) contract_result_in_scope: bool,
}

impl DeclaredScope<'_> {
    /// The C declaration `name` spells here, resolved through the bindings
    /// in scope, unless the proof binds the spelling itself.
    fn c_name(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<crate::kernel::BindingName> {
        let crate::surface::binders::BinderKeyRef::Written(spelling) = name.binder_key()? else {
            return None;
        };
        if self.integer_values.contains_key(spelling)
            || self.algebraic_values.contains_key(spelling)
        {
            return None;
        }
        Some(self.declarations.source_binding(spelling.into()))
    }

    /// The declared C type of `name`, as written: an array keeps its array
    /// type.
    fn declared_type(&self, name: &dyn crate::surface::binders::BinderKey) -> Option<ProgramType> {
        self.declarations.c_variable_type(self.c_name(name)?)
    }

    /// The struct a resolved C declaration of struct or struct-pointer type
    /// names.
    fn declared_struct(&self, name: &dyn crate::surface::binders::BinderKey) -> Option<String> {
        let name = self.c_name(name)?;
        name.local_id()
            .and_then(|id| id.struct_name())
            .or_else(|| name.static_id().and_then(|id| id.struct_name()))
            .map(str::to_owned)
    }
}

impl TypeScope for DeclaredScope<'_> {
    fn binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        if self.integer_values.contains_key(name) {
            return Some(ClickType::Integer);
        }
        if let Some(click_type) = self.algebraic_binding_click_type(name) {
            return Some(click_type);
        }
        self.program_binding_click_type(name)
    }
    fn algebraic_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        self.algebraic_values.get(name).map(|value| {
            generics::click_type_from_algebraic_value_type(&value.algebraic_type.value_type())
        })
    }
    fn is_integer_binding(&self, name: &dyn crate::surface::binders::BinderKey) -> bool {
        self.integer_values.contains_key(name)
    }
    fn binding_is_algebraic(&self, name: &dyn crate::surface::binders::BinderKey) -> bool {
        self.algebraic_values.contains_key(name)
    }
    fn bound_array_element_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        self.declared_type(name)?.array_element_type()
    }
    fn bound_pointer_pointee_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        self.declared_type(name)
            .filter(|ty| ty.is_pointer())?
            .pointee_type()
    }
    fn bound_enum_value_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        None
    }
    fn program_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        let ty = self.declared_type(name)?;
        // In an expression an array names a pointer to its first element.
        let ty = match ty.array_element_type() {
            Some(element) => element.pointer_to()?,
            None => ty,
        };
        let interface_type = generics::interface_type_from_program_type(ty);
        Some(match self.declared_struct(name) {
            Some(struct_name) if ty.is_pointer() => ClickType::CObjectPointer {
                interface_type,
                struct_name,
            },
            Some(_) => return None,
            None => ClickType::Program(interface_type),
        })
    }
    fn bound_pointer_element(&self, name: &crate::kernel::BindingName) -> Option<PointerElement> {
        let ty = self
            .declarations
            .c_variable_type(self.declarations.source_binding(name.clone()))
            .filter(|ty| ty.is_pointer())?;
        let name = self.declarations.source_binding(name.clone());
        let struct_name = name
            .local_id()
            .and_then(|id| id.struct_name())
            .or_else(|| name.static_id().and_then(|id| id.struct_name()));
        Some(match struct_name {
            Some(struct_name) => PointerElement::Struct(struct_name.to_owned()),
            None => PointerElement::Pointee(ty.pointee_type()),
        })
    }
    fn at_entry(&self, _: &PointInputs<'_>) -> Result<Box<dyn TypeScope + '_>, String> {
        Ok(Box::new(*self))
    }
    fn at_point(
        &self,
        _: &ProgramPointSelector,
        _: &PointInputs<'_>,
    ) -> Result<Option<Box<dyn TypeScope + '_>>, String> {
        Ok(Some(Box::new(*self)))
    }
    fn call_result_point(&self) -> Option<&ProgramPointSelector> {
        None
    }
    fn contract_result_in_scope(&self) -> bool {
        self.contract_result_in_scope
    }
}
