//! The declarations elaboration and lowering read names' types from: the
//! function's parameters and result, its entry values and states, and the
//! recorded types of locals (`design/typed-surface.md`). A `Declarations`
//! borrows nothing from the lowerer that holds it, so elaboration can read
//! it while the lowerer is in use.
use super::*;

#[derive(Clone)]
pub(super) struct Declarations<'a> {
    pub(super) source_bindings: Option<syntax::CSourceBindings>,
    pub(super) entry_state: &'a ExecutionState,
    pub(super) result_type: ProgramType,
    pub(super) entry_values: Arc<ProgramValueBindings>,
    pub(super) local_type_state: Option<&'a ExecutionState>,
    pub(super) program_parameter_types: Arc<BTreeMap<String, ProgramType>>,
    pub(super) pointer_element_types: Arc<BTreeMap<String, ProgramType>>,
}

impl<'a> AnnotationLowerer<'a> {
    /// The lowerer's declarations, as a value independent of the lowerer.
    pub(super) fn declarations(&self) -> Declarations<'a> {
        Declarations {
            source_bindings: self.source_bindings.clone(),
            entry_state: self.entry_state,
            result_type: self.result_type,
            entry_values: self.entry_values.clone(),
            local_type_state: self.local_type_state,
            program_parameter_types: self.program_parameter_types.clone(),
            pointer_element_types: self.pointer_element_types.clone(),
        }
    }
}

impl Declarations<'_> {
    pub(super) fn source_binding(
        &self,
        name: crate::kernel::BindingName,
    ) -> crate::kernel::BindingName {
        name.named()
            .and_then(|name| self.source_bindings.as_ref()?.get(name))
            .map(|(_, binding)| binding.clone())
            .unwrap_or(name)
    }

    pub(super) fn declared_pointer_element_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
    ) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return self
                .result_type
                .pointee_type()
                .or_else(|| self.result_type.array_element_type());
        }
        // A resolved local carries its declared type when lowering recorded
        // one; a local named by selector (`f.statement(3).local(word)`) may
        // not, and then reads its type from the state that declares it.
        if name.unresolved_name().is_none()
            && let Some(element) = name
                .program_type()
                .and_then(|ty| ty.pointee_type().or_else(|| ty.array_element_type()))
        {
            return Some(element);
        }
        self.local_type_state
            .and_then(|state| {
                state
                    .local_object_type(&name)
                    .and_then(|ty| ty.pointee_type())
                    // A local array, such as `char tmp[12]`, is indexed by
                    // its element type, as a fixed-state proof reads it.
                    .or_else(|| state.locals().array_object_element_type(&name))
            })
            .or_else(|| {
                name.metadata_in(self.pointer_element_types.as_ref())
                    .copied()
            })
    }

    /// The declared C type of a parameter or local named in a clause, from
    /// its typed entry value or the live declaration state.
    pub(super) fn c_variable_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
    ) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return Some(self.result_type);
        }
        if name.unresolved_name().is_none() {
            return name.program_type();
        }
        name.metadata_in(self.program_parameter_types.as_ref())
            .copied()
            .or_else(|| {
                name.metadata_in(self.entry_values.as_ref())
                    .map(ProgramValue::program_type)
            })
            .or_else(|| {
                self.entry_state
                    .locals()
                    .get(&name)
                    .map(|value| value.program_type())
            })
            .or_else(|| {
                self.local_type_state
                    .and_then(|state| state.local_object_type(&name))
            })
    }
}
