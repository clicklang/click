//! Values retained between evaluation and execution boundaries.
//! Compatibility reads are explicit; a shared value owns only its common root.
use super::prelude::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum ExecutionValue {
    Native(CValue),
    Shared(KernelTerm),
}

impl From<CValue> for ExecutionValue {
    fn from(value: CValue) -> Self {
        Self::Native(value)
    }
}
impl From<KernelTerm> for ExecutionValue {
    fn from(value: KernelTerm) -> Self {
        Self::Shared(value)
    }
}
impl ExecutionValue {
    /// Import a native machine producer's result once at its execution boundary.
    /// Other result families keep their exact native payloads.
    pub(in crate::kernel) fn retain_native(value: CValue) -> Self {
        if let crate::kernel::integer_c_value!(term) = &value {
            // Scalar leaves have no expression prefix to retain. Keep their
            // existing cheap reading, including condition truth values.
            if matches!(
                term,
                MachineTerm::Constant { .. } | MachineTerm::Variable(_)
            ) {
                return Self::Native(value);
            }
            let format = MachineIntegerType::from_c_type(value.c_type()).unwrap();
            return Self::Shared(KernelTermImport::default().machine(format, term));
        }
        Self::Native(value)
    }

    pub(in crate::kernel) fn into_native(self) -> CValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(term) => {
                if matches!(term.node(), KernelTermNode::Call { .. }) {
                    let KernelType::C(ty) = term.ty() else {
                        unreachable!()
                    };
                    let format =
                        MachineIntegerType::from_c_type(*ty).expect("machine call result type");
                    // The native result carrier needs only this call root.
                    // Keep numeric argument DAGs shared across the handoff;
                    // explicit KernelTermExport remains the structural export.
                    return format.value_from_term(
                        term.machine_conversion_leaf()
                            .expect("machine call root")
                            .clone(),
                    );
                }
                let PureFunctionArgument::Value(value) = KernelTermExport::default()
                    .argument(&term)
                    .expect("machine expression result")
                else {
                    unreachable!()
                };
                value
            }
        }
    }
    pub(in crate::kernel) fn native(&self) -> std::borrow::Cow<'_, CValue> {
        match self {
            Self::Native(value) => std::borrow::Cow::Borrowed(value),
            Self::Shared(_) => std::borrow::Cow::Owned(self.clone().into_native()),
        }
    }
    pub(in crate::kernel) fn c_type(&self) -> CType {
        match self {
            Self::Native(value) => value.c_type(),
            Self::Shared(term) => match term.ty() {
                KernelType::C(ty) => *ty,
                _ => unreachable!(),
            },
        }
    }
    pub(in crate::kernel) fn machine(
        &self,
    ) -> Option<(MachineIntegerType, MachineOperandView<'_>)> {
        let format = MachineIntegerType::from_c_type(self.c_type())?;
        match self {
            Self::Native(value) => {
                let (crate::kernel::integer_c_value!(term)) = value else {
                    return None;
                };
                Some((format, MachineOperandView::Legacy(term)))
            }
            Self::Shared(term) => Some((format, MachineOperandView::Shared(term))),
        }
    }
}

impl<V> CExpressionPath<V> {
    pub(in crate::kernel) fn map_value<W>(self, map: impl FnOnce(V) -> W) -> CExpressionPath<W> {
        CExpressionPath {
            outcome: self.outcome.map_value(map),
            facts: self.facts,
            obligations: self.obligations,
        }
    }
}

impl From<CExpressionPath> for CExpressionPath<ExecutionValue> {
    fn from(path: CExpressionPath) -> Self {
        path.map_value(ExecutionValue::retain_native)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn execution_outcomes_preserve_native_values_and_refusals() {
        let value = CValue::Int32(MachineTerm::constant(7));
        let outcome = CExpressionOutcome::Value(value.clone()).map_value(ExecutionValue::from);
        assert_eq!(
            outcome.map_value(ExecutionValue::into_native),
            CExpressionOutcome::Value(value)
        );
        let undefined =
            CExpressionOutcome::<CValue>::UndefinedBehavior(CUndefinedBehavior::SignedOverflow);
        assert_eq!(
            undefined
                .clone()
                .map_value(ExecutionValue::from)
                .map_value(ExecutionValue::into_native),
            undefined
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/execution_value.rs");
}
