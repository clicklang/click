//! Algebraic evaluator results. Symbolic matches retain their common roots;
//! consumers of the remaining native algebraic representation cross an
//! explicit compatibility boundary.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum AlgebraicResult {
    Native(AlgebraicTerm),
    Shared(KernelTerm),
}

impl From<AlgebraicTerm> for AlgebraicResult {
    fn from(value: AlgebraicTerm) -> Self {
        Self::Native(value)
    }
}

impl AlgebraicResult {
    pub(super) fn algebraic_type(&self) -> &AlgebraicType {
        match self {
            Self::Native(value) => &value.algebraic_type,
            Self::Shared(root) => {
                let KernelType::Algebraic(ty) = root.ty() else {
                    unreachable!("algebraic result type");
                };
                ty
            }
        }
    }

    pub(super) fn is_constructor(&self) -> bool {
        match self {
            Self::Native(value) => matches!(value.node, AlgebraicTermNode::Constructor { .. }),
            Self::Shared(root) => matches!(root.node(), KernelTermNode::Constructor(_)),
        }
    }
    pub(super) fn retain_native(value: AlgebraicTerm, retain: bool) -> Self {
        if retain {
            Self::Shared(KernelTermImport::default().algebraic(&value))
        } else {
            Self::Native(value)
        }
    }

    pub(super) fn native_constructor(&self) -> Option<&AlgebraicTerm> {
        match self {
            Self::Native(value) if matches!(value.node, AlgebraicTermNode::Constructor { .. }) => {
                Some(value)
            }
            Self::Shared(root) if matches!(root.node(), KernelTermNode::Constructor(_)) => {
                let ProgramValue::Parameter(value) = root.algebraic_native_value()? else {
                    unreachable!()
                };
                Some(value)
            }
            _ => None,
        }
    }

    pub(super) fn into_kernel(self) -> KernelTerm {
        match self {
            Self::Native(value) => {
                KernelTermImport::default().argument(&PureFunctionArgument::Algebraic(value))
            }
            Self::Shared(root) => root,
        }
    }

    pub(super) fn into_native_compat(self) -> AlgebraicTerm {
        match self {
            Self::Native(value) => value,
            Self::Shared(root) => KernelTermExport::default()
                .algebraic(&root)
                .expect("algebraic result compatibility boundary"),
        }
    }
}

/// A selected constructor field. Program-carried parameters keep their native
/// field form at the mixed-family boundary; logical algebraic fields retain roots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum AlgebraicFieldResult {
    Native(AlgebraicValue),
    Shared(KernelTerm),
}

impl AlgebraicFieldResult {
    pub(super) fn from_program(value: SpecValue) -> Self {
        match value {
            SpecValue::Shared(root) if !matches!(root.ty(), KernelType::Algebraic(_)) => {
                Self::Shared(root)
            }
            value => Self::Native(AlgebraicValue::Program(value.into_native())),
        }
    }
    pub(super) fn from_algebraic(value: AlgebraicResult) -> Self {
        match value {
            AlgebraicResult::Native(value) => Self::Native(AlgebraicValue::Algebraic(value)),
            AlgebraicResult::Shared(root) => Self::Shared(root),
        }
    }
    pub(super) fn has_type(&self, expected: &AlgebraicValueType) -> bool {
        match self {
            Self::Native(value) => value.has_type(expected),
            Self::Shared(root) => match root.ty() {
                KernelType::Algebraic(ty) => ty.value_type() == *expected,
                KernelType::Integer => *expected == AlgebraicValueType::Integer,
                KernelType::Bool => *expected == AlgebraicValueType::Program(ProgramType::Bool),
                KernelType::Program(ty) => match expected {
                    AlgebraicValueType::Program(expected) => ty == expected,
                    AlgebraicValueType::ObjectPointer(_, _) => SpecValue::Shared(root.clone())
                        .native_payload()
                        .is_some_and(|value| expected.accepts_program_value(value)),
                    _ => false,
                },
                _ => false,
            },
        }
    }
    pub(super) fn program_mut(&mut self) -> Option<&mut ProgramValue> {
        if let Self::Shared(root) = self {
            if !matches!(root.ty(), KernelType::Program(ty) if ty.is_pointer()) {
                return None;
            }
            *self = Self::Native(AlgebraicValue::Program(
                SpecValue::Shared(root.clone()).into_native(),
            ));
        }
        match self {
            Self::Native(AlgebraicValue::Program(value)) => Some(value),
            _ => None,
        }
    }
    pub(super) fn without_pointer_constant(mut self) -> Self {
        match self {
            Self::Native(AlgebraicValue::Program(value)) => Self::Native(AlgebraicValue::Program(
                value.with_pointer_pointee_constant(false),
            )),
            Self::Shared(ref root) if matches!(root.ty(), KernelType::Program(ty) if ty.is_pointer()) =>
            {
                if let Some(value) = self.program_mut() {
                    *value = value.clone().with_pointer_pointee_constant(false);
                }
                self
            }
            _ => self,
        }
    }
    pub(super) fn into_kernel(self) -> KernelTerm {
        match self {
            Self::Shared(root) => root,
            Self::Native(AlgebraicValue::Algebraic(value)) => {
                KernelTermImport::default().algebraic(&value)
            }
            Self::Native(value) => KernelTermImport::default().match_field(&value),
        }
    }
    pub(super) fn into_native(self) -> AlgebraicValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(root) => match KernelTermExport::default()
                .argument(&root)
                .expect("selected field output")
            {
                PureFunctionArgument::Value(value) => AlgebraicValue::Program(value),
                PureFunctionArgument::Integer(value) => {
                    AlgebraicValue::Integer(value.as_ref().clone())
                }
                PureFunctionArgument::Algebraic(value) => AlgebraicValue::Algebraic(value),
                _ => unreachable!("constructor field"),
            },
        }
    }
    pub(super) fn integer(&self) -> Option<IntegerTerm> {
        match self {
            Self::Native(AlgebraicValue::Integer(value)) => Some(value.clone()),
            Self::Shared(root) if root.ty() == &KernelType::Integer => Some(
                KernelTermExport::default()
                    .integer(root)
                    .expect("Integer binding")
                    .as_ref()
                    .clone(),
            ),
            _ => None,
        }
    }
    pub(super) fn bind(
        &self,
        name: &BindingName,
        state: &mut ExecutionState,
        algebraic: &mut BTreeMap<BindingName, AlgebraicTerm>,
        values: &mut crate::persistent::PersistentMap<BindingName, KernelTerm>,
    ) {
        match self {
            Self::Shared(root) if matches!(root.node(), KernelTermNode::Legacy(_)) => self
                .clone()
                .into_native_result()
                .bind(name, state, algebraic, values),
            Self::Shared(root) if root.ty() != &KernelType::Integer => {
                values.insert(name.to_owned(), root.clone());
            }
            Self::Shared(_) | Self::Native(AlgebraicValue::Integer(_)) => {}
            Self::Native(AlgebraicValue::Program(value)) => {
                super::bindings::bind_value(name, value.clone().into(), state, values);
            }
            Self::Native(AlgebraicValue::Algebraic(value)) => {
                algebraic.insert(name.to_owned(), value.clone());
            }
        }
    }
    fn into_native_result(self) -> Self {
        Self::Native(self.into_native())
    }
}
