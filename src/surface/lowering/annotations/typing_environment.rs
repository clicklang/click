//! The typing environment elaboration reads (`design/typed-surface.md`).
//!
//! Elaboration decides kinds from the types of the names in scope. A name
//! bound inside the proposition being elaborated (a quantifier, a `let`, a
//! match arm) has the type its declaration gives it, recorded in `binders`.
//! A name bound outside it (a parameter, a theorem argument, a proof local)
//! is looked up in the lowering context the proposition is elaborated in,
//! which today knows a name's type only through the value it lowered the name
//! to; `SpecElaborationContext`'s typing methods read that.
//!
//! A binder shadows an outer name of the same spelling, as lowering's own
//! scoping removes the outer entry when it binds one.
use super::*;

pub(super) struct TypingEnvironment<'a> {
    outer: &'a SpecElaborationContext,
    binders: PersistentBinderMap<ClickType>,
}

impl<'a> TypingEnvironment<'a> {
    /// The typing environment of a lowering context, with no binders of its
    /// own.
    pub(super) fn of(outer: &'a SpecElaborationContext) -> Self {
        Self {
            outer,
            binders: PersistentBinderMap::default(),
        }
    }

    /// The type a name has here.
    pub(super) fn binding_click_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ClickType> {
        match self.binders.get(name) {
            Some(click_type) => Some(click_type.clone()),
            None => self.outer.binding_click_type(name),
        }
    }

    /// The type of a name bound to an algebraic value: an algebraic binder's
    /// declared type, or an outer algebraic binding's.
    pub(super) fn algebraic_binding_click_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ClickType> {
        match self.binders.get(name) {
            Some(click_type @ ClickType::Algebraic(_)) => Some(click_type.clone()),
            Some(_) => None,
            None => self.outer.algebraic_binding_click_type(name),
        }
    }

    /// Whether a name is bound to an algebraic value.
    pub(super) fn binding_is_algebraic<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> bool {
        match self.binders.get(name) {
            Some(click_type) => matches!(click_type, ClickType::Algebraic(_)),
            None => self.outer.binding_is_algebraic(name),
        }
    }

    /// The element type of a name bound to an array reference. A binder is
    /// never one: lowering drops the outer name's array reference when it
    /// binds the name.
    pub(super) fn bound_array_element_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ProgramType> {
        match self.binders.get(name) {
            Some(_) => None,
            None => self.outer.bound_array_element_type(name),
        }
    }

    /// The pointee type of a name bound to a pointer: a pointer binder's
    /// declared pointee, or an outer name's lowered pointer's.
    pub(super) fn bound_pointer_pointee_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ProgramType> {
        match self.binders.get(name) {
            Some(click_type) => click_type
                .interface_type()
                .map(InterfaceType::to_kernel_type)
                .and_then(ProgramType::pointee_type),
            None => self.outer.bound_pointer_pointee_type(name),
        }
    }

    /// The program type of a name bound to an enum or library value: a
    /// binder's declared type when it is one, or an outer name's lowered
    /// value's.
    pub(super) fn bound_enum_value_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ProgramType> {
        match self.binders.get(name) {
            Some(click_type) => click_type
                .interface_type()
                .map(InterfaceType::to_kernel_type)
                .filter(|ty| matches!(ty, ProgramType::Parameter(_))),
            None => self.outer.bound_enum_value_type(name),
        }
    }

    /// The call whose result `result` and region results name here.
    pub(super) fn call_result_point(&self) -> Option<&'a ProgramPointSelector> {
        self.outer.call_result_point.as_ref()
    }

    /// Whether bare `result` names the contract's return value here.
    pub(super) fn contract_result_in_scope(&self) -> bool {
        self.outer.contract_result_in_scope
    }

    /// The type of a name read as a program binding. Lowering keeps an
    /// Integer binder in `integer_values` and an algebraic one in
    /// `algebraic_values`, and every other binder in `values`, which is all a
    /// program binding reads; a binder's type answers the same way.
    pub(super) fn program_binding_click_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ClickType> {
        match self.binders.get(name) {
            Some(ClickType::Integer | ClickType::Algebraic(_)) => None,
            Some(click_type) => Some(click_type.clone()),
            None => self.outer.program_binding_click_type(name),
        }
    }
}
