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

    /// The C type of C name `name`, a parameter, local or `result`, unless a
    /// spec binding shadows it.
    pub(super) fn program_name_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return Some(self.result_type);
        }
        if matches!(name, crate::kernel::BindingName::Generated(_)) {
            return typing
                .program_binding_click_type(&name)
                .and_then(|ty| ty.interface_type())
                .map(|ty| ty.to_kernel_type());
        }
        if name.unresolved_name().is_none() {
            return name.program_type();
        }
        if typing.binding_is_algebraic(&name) {
            return None;
        }
        if name.is_named("result") {
            Some(self.result_type)
        } else {
            name.metadata_in(self.program_parameter_types.as_ref())
                .copied()
                .or_else(|| {
                    name.metadata_in(self.entry_values.as_ref())
                        .map(ProgramValue::program_type)
                        .or_else(|| {
                            self.local_type_state
                                .and_then(|state| state.locals().get(&name))
                                .map(|value| value.program_type())
                        })
                        // A name bound to a value in this context: a fixed state's
                        // local, including one that keeps an enum in memory.
                        .or_else(|| typing.bound_enum_value_type(&name))
                })
        }
    }

    pub(super) fn program_expression_array_element_type(
        &self,
        expression: &ProgramExpression,
        typing: &TypingEnvironment<'_>,
    ) -> Option<ProgramType> {
        if matches!(expression, ProgramExpression::Variable(name) if name.is_named("result"))
            && typing.contract_result_in_scope()
        {
            return self.program_expression_array_element_type(
                &ProgramExpression::Variable(crate::kernel::CONTRACT_RESULT),
                typing,
            );
        }
        match expression {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => {
                pointer.program_type().pointee_type()
            }
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) => match target.as_ref() {
                ProgramExpression::TypedLoad { value_type, .. } => Some(*value_type),
                ProgramExpression::Variable(name) => self.c_variable_type(name),
                // `&p[i]` and `&*p` point at `p`'s element: `*&p[i]` reads
                // what `p[i]` reads, not an `int32`.
                ProgramExpression::Index(base, _) | ProgramExpression::Load(base) => {
                    self.program_expression_array_element_type(base, typing)
                }
                _ => None,
            },
            ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
            ProgramExpression::Variable(name) => typing
                .bound_array_element_type(name)
                .or_else(|| self.declared_pointer_element_type(name))
                .or_else(|| {
                    (name == &crate::kernel::CONTRACT_RESULT)
                        .then(|| self.result_type.pointee_type())
                        .flatten()
                })
                .or_else(|| self.entry_state.global_array_element_type(name))
                // A C++ reference's carrier is declared as a pointer to its
                // referent.
                .or_else(|| {
                    name.reference_referent()
                        .and_then(|_| self.c_variable_type(name.clone()))
                        .and_then(ProgramType::pointee_type)
                })
                // A pointer global reads at its declared pointee.
                .or_else(|| {
                    self.entry_state
                        .global_object_type(name)
                        .and_then(ProgramType::pointee_type)
                })
                .or_else(|| typing.bound_pointer_pointee_type(name)),
            ProgramExpression::TypedLoad { value_type, .. } => match value_type {
                ProgramType::Int32Array(_) => Some(ProgramType::Int32),
                ProgramType::UInt32Array(_) => Some(ProgramType::UInt32),
                ProgramType::Int64Array(_) => Some(ProgramType::Int64),
                ProgramType::Int128Array(_) => Some(ProgramType::Int128),
                ProgramType::UInt64Array(_) => Some(ProgramType::UInt64),
                ProgramType::UInt128Array(_) => Some(ProgramType::UInt128),
                ProgramType::UInt8Array(_) => Some(ProgramType::UInt8),
                value_type => value_type.pointee_type(),
            },
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => {
                self.program_expression_array_element_type(pointer, typing)
            }
            ProgramExpression::Add(left, right) => self
                .program_expression_array_element_type(left, typing)
                .or_else(|| self.program_expression_array_element_type(right, typing)),
            ProgramExpression::Subtract(left, _) => {
                self.program_expression_array_element_type(left, typing)
            }
            // `*pp` and `pp[i]` hold `pp`'s pointer element, which points at
            // that pointer's pointee.
            ProgramExpression::Load(pointer) | ProgramExpression::Index(pointer, _) => self
                .program_expression_array_element_type(pointer, typing)
                .and_then(ProgramType::pointee_type),
            _ => None,
        }
    }
}
