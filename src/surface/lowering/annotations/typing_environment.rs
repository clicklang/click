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

/// What elaboration may ask about the names bound outside the proposition it
/// elaborates: their types, and the two facts about the clause's position
/// that name resolution needs. Elaboration reads outer names only through
/// this, so it does not depend on how a scope knows the answers. The
/// lowering context answers from the values lowering bound the names to; a
/// scope built from declarations can answer with no kernel at all.
pub(super) trait TypeScope {
    /// The type a name has.
    fn binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType>;
    /// The type of a name bound to an algebraic value.
    fn algebraic_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType>;
    /// Whether a name is bound to an Integer.
    fn is_integer_binding(&self, name: &dyn crate::surface::binders::BinderKey) -> bool;
    /// Whether a name is bound to an algebraic value.
    fn binding_is_algebraic(&self, name: &dyn crate::surface::binders::BinderKey) -> bool;
    /// The element type of a name bound to an array reference.
    fn bound_array_element_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType>;
    /// The pointee type of a name bound to a pointer.
    fn bound_pointer_pointee_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType>;
    /// The program type of a name bound to an enum or library value.
    fn bound_enum_value_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType>;
    /// The type of a name read as a program binding.
    fn program_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType>;
    /// What the pointer a C name is directly bound to steps by: a resolved
    /// local's current pointer, or a pointer value the name is bound to.
    fn bound_pointer_element(&self, name: &crate::kernel::BindingName) -> Option<PointerElement>;
    /// The call whose result `result` and region results name here.
    fn call_result_point(&self) -> Option<&ProgramPointSelector>;
    /// Whether bare `result` names the contract's return value here.
    fn contract_result_in_scope(&self) -> bool;
}

/// The lowering context answers from the values lowering bound each name to,
/// with the lookups elaboration used before this boundary existed.
impl TypeScope for SpecElaborationContext {
    fn binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        Self::binding_click_type(self, name)
    }
    fn algebraic_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        Self::algebraic_binding_click_type(self, name)
    }
    fn is_integer_binding(&self, name: &dyn crate::surface::binders::BinderKey) -> bool {
        self.integer_values.contains_key(name)
    }
    fn binding_is_algebraic(&self, name: &dyn crate::surface::binders::BinderKey) -> bool {
        Self::binding_is_algebraic(self, name)
    }
    fn bound_array_element_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        Self::bound_array_element_type(self, name)
    }
    fn bound_pointer_pointee_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        Self::bound_pointer_pointee_type(self, name)
    }
    fn bound_enum_value_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        Self::bound_enum_value_type(self, name)
    }
    fn program_binding_click_type(
        &self,
        name: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        Self::program_binding_click_type(self, name)
    }
    fn bound_pointer_element(&self, name: &crate::kernel::BindingName) -> Option<PointerElement> {
        if name.local_id().is_some()
            && let Some(state) = self.reference_state.as_ref()
        {
            return state.locals().get(name)?.pointer().map(PointerElement::of);
        }
        match name.named_in(&self.values) {
            Some(SpecExpression::Value(ProgramValue::Pointer(pointer))) => {
                Some(PointerElement::of(pointer))
            }
            _ => None,
        }
    }
    fn call_result_point(&self) -> Option<&ProgramPointSelector> {
        self.call_result_point.as_ref()
    }
    fn contract_result_in_scope(&self) -> bool {
        self.contract_result_in_scope
    }
}

/// An outer scope with no names in it: every name a typing environment over
/// it knows is one it binds with a declared type. Elaboration over it reads
/// nothing lowering built.
#[cfg(test)]
pub(super) struct NoOuterNames;

#[cfg(test)]
impl TypeScope for NoOuterNames {
    fn binding_click_type(&self, _: &dyn crate::surface::binders::BinderKey) -> Option<ClickType> {
        None
    }
    fn algebraic_binding_click_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        None
    }
    fn is_integer_binding(&self, _: &dyn crate::surface::binders::BinderKey) -> bool {
        false
    }
    fn binding_is_algebraic(&self, _: &dyn crate::surface::binders::BinderKey) -> bool {
        false
    }
    fn bound_array_element_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        None
    }
    fn bound_pointer_pointee_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        None
    }
    fn bound_enum_value_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ProgramType> {
        None
    }
    fn program_binding_click_type(
        &self,
        _: &dyn crate::surface::binders::BinderKey,
    ) -> Option<ClickType> {
        None
    }
    fn bound_pointer_element(&self, _: &crate::kernel::BindingName) -> Option<PointerElement> {
        None
    }
    fn call_result_point(&self) -> Option<&ProgramPointSelector> {
        None
    }
    fn contract_result_in_scope(&self) -> bool {
        false
    }
}

pub(super) struct TypingEnvironment<'a> {
    outer: &'a dyn TypeScope,
    binders: PersistentBinderMap<ClickType>,
    /// The call `at(call, ..)` names inside the term being typed, in place
    /// of the outer scope's.
    call_result_point: Option<&'a ProgramPointSelector>,
}

impl<'a> TypingEnvironment<'a> {
    /// The typing environment of a lowering context, with no binders of its
    /// own.
    pub(super) fn of(outer: &'a SpecElaborationContext) -> Self {
        Self::in_scope(outer)
    }

    /// The typing environment of any outer scope, with no binders of its own.
    pub(super) fn in_scope(outer: &'a dyn TypeScope) -> Self {
        Self {
            outer,
            binders: PersistentBinderMap::default(),
            call_result_point: None,
        }
    }

    /// This environment inside `at(selector, ..)`: `result` and region
    /// results name `selector`'s call.
    pub(super) fn at_call<'b>(&self, selector: &'b ProgramPointSelector) -> TypingEnvironment<'b>
    where
        'a: 'b,
    {
        TypingEnvironment {
            outer: self.outer,
            binders: self.binders.clone(),
            call_result_point: Some(selector),
        }
    }

    /// Bind `name` with the type its declaration gives it. Every typing
    /// query then answers for `name` from that type alone, as
    /// `check_declared_binder` checks lowering does too.
    #[cfg(test)]
    pub(super) fn declare(
        &mut self,
        name: impl Into<crate::surface::binders::SurfaceBinder>,
        declared: ClickType,
    ) {
        self.binders.insert(name.into(), declared);
    }

    /// The type a name has here.
    pub(super) fn binding_click_type<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> Option<ClickType> {
        match self.binders.get(name) {
            Some(click_type) => Some(click_type.clone()),
            None => self.outer.binding_click_type(&name),
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
            None => self.outer.algebraic_binding_click_type(&name),
        }
    }

    /// Whether a name is bound to an Integer: an Integer binder, or an outer
    /// name lowering bound among the Integer bindings.
    pub(super) fn is_integer_binding<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> bool {
        match self.binders.get(name) {
            Some(click_type) => *click_type == ClickType::Integer,
            None => self.outer.is_integer_binding(&name),
        }
    }

    /// Whether a name is bound to an algebraic value.
    pub(super) fn binding_is_algebraic<Q: crate::surface::binders::BinderKey + ?Sized>(
        &self,
        name: &Q,
    ) -> bool {
        match self.binders.get(name) {
            Some(click_type) => matches!(click_type, ClickType::Algebraic(_)),
            None => self.outer.binding_is_algebraic(&name),
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
            None => self.outer.bound_array_element_type(&name),
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
            None => self.outer.bound_pointer_pointee_type(&name),
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
            None => self.outer.bound_enum_value_type(&name),
        }
    }

    /// The call whose result `result` and region results name here.
    pub(super) fn call_result_point(&self) -> Option<&'a ProgramPointSelector> {
        self.call_result_point
            .or_else(|| self.outer.call_result_point())
    }

    /// What the pointer a C name is directly bound to steps by. A binder is
    /// never bound to a pointer value: lowering binds it to its variable.
    pub(super) fn bound_pointer_element(
        &self,
        name: &crate::kernel::BindingName,
    ) -> Option<PointerElement> {
        match self.binders.get(name) {
            Some(_) => None,
            None => self.outer.bound_pointer_element(name),
        }
    }

    /// Whether bare `result` names the contract's return value here.
    pub(super) fn contract_result_in_scope(&self) -> bool {
        self.outer.contract_result_in_scope()
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
            None => self.outer.program_binding_click_type(&name),
        }
    }
}

/// Check that a binder's declared type answers every typing query exactly as
/// the value lowering bound it to: the property that lets elaboration type a
/// binder from its declaration, before anything is lowered
/// (`design/typed-surface.md`). `lowered` is the context lowering built for
/// the binder's body.
#[cfg(test)]
pub(super) fn check_declared_binder(
    name: &SurfaceBinder,
    declared: &ClickType,
    lowered: &SpecElaborationContext,
) {
    let by_value = TypingEnvironment::of(lowered);
    let mut by_type = TypingEnvironment::of(lowered);
    by_type.declare(name, declared.clone());
    let binding_name = match name {
        SurfaceBinder::Written(written) => crate::kernel::BindingName::Named(written.clone()),
        SurfaceBinder::Generated(id) => crate::kernel::BindingName::Generated(*id),
    };
    let pairs: [(&str, String, String); 8] = [
        (
            "bound_pointer_element",
            format!("{:?}", by_type.bound_pointer_element(&binding_name)),
            format!("{:?}", by_value.bound_pointer_element(&binding_name)),
        ),
        (
            "binding_click_type",
            format!("{:?}", by_type.binding_click_type(name)),
            format!("{:?}", by_value.binding_click_type(name)),
        ),
        (
            "program_binding_click_type",
            format!("{:?}", by_type.program_binding_click_type(name)),
            format!("{:?}", by_value.program_binding_click_type(name)),
        ),
        (
            "algebraic_binding_click_type",
            format!("{:?}", by_type.algebraic_binding_click_type(name)),
            format!("{:?}", by_value.algebraic_binding_click_type(name)),
        ),
        (
            "binding_is_algebraic",
            format!("{:?}", by_type.binding_is_algebraic(name)),
            format!("{:?}", by_value.binding_is_algebraic(name)),
        ),
        (
            "bound_array_element_type",
            format!("{:?}", by_type.bound_array_element_type(name)),
            format!("{:?}", by_value.bound_array_element_type(name)),
        ),
        (
            "bound_pointer_pointee_type",
            format!("{:?}", by_type.bound_pointer_pointee_type(name)),
            format!("{:?}", by_value.bound_pointer_pointee_type(name)),
        ),
        (
            "bound_enum_value_type",
            format!("{:?}", by_type.bound_enum_value_type(name)),
            format!("{:?}", by_value.bound_enum_value_type(name)),
        ),
    ];
    for (query, typed, lowered) in pairs {
        assert_eq!(
            typed, lowered,
            "binder `{name:?}` declared `{declared:?}`: `{query}` answers differently from its lowered value"
        );
    }
}
