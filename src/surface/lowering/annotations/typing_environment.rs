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
