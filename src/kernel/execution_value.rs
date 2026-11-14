//! Values retained between evaluation and execution boundaries.
//! Compatibility reads are explicit; a shared value owns only its common root.
use super::prelude::*;

#[derive(Clone, Debug, Eq)]
pub enum ExecutionValue {
    Native(ProgramValue),
    Shared(KernelTerm),
}

impl PartialEq for ExecutionValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Native(a), Self::Native(b)) => a == b,
            (Self::Shared(a), Self::Shared(b)) => {
                a == b
                    || (a.ty() == b.ty()
                        && (a.has_machine_matches() || b.has_machine_matches())
                        && crate::kernel::shared_machine_syntax_equal(a, b))
            }
            _ => false,
        }
    }
}

impl From<ProgramValue> for ExecutionValue {
    fn from(value: ProgramValue) -> Self {
        Self::Native(value)
    }
}
impl From<KernelTerm> for ExecutionValue {
    fn from(value: KernelTerm) -> Self {
        Self::Shared(value)
    }
}
impl ExecutionValue {
    pub fn shared(&self) -> Option<&KernelTerm> {
        match self {
            Self::Shared(root) => Some(root),
            Self::Native(_) => None,
        }
    }
    pub fn native_payload(&self) -> Option<&ProgramValue> {
        match self {
            Self::Native(value) => Some(value),
            Self::Shared(_) => None,
        }
    }
    pub fn pointer(&self) -> Option<&PointerValue> {
        match self.native_payload()? {
            ProgramValue::Pointer(pointer) => Some(pointer),
            _ => None,
        }
    }
    pub fn byte_width(&self) -> u32 {
        self.program_type().byte_width()
    }
    /// Import a native machine producer's result once at its execution boundary.
    /// Other result families keep their exact native payloads.
    pub(in crate::kernel) fn retain_native(value: ProgramValue) -> Self {
        if let crate::kernel::integer_c_value!(term) = &value {
            // Scalar leaves have no expression prefix to retain. Keep their
            // existing cheap reading, including condition truth values.
            if matches!(
                term,
                MachineTerm::Constant { .. } | MachineTerm::Variable(_)
            ) {
                return Self::Native(value);
            }
            let format = MachineIntegerType::from_program_type(value.program_type()).unwrap();
            if let Some(root) = KernelTermImport::default().machine_arithmetic(format, term) {
                return Self::Shared(root);
            }
        }
        Self::Native(value)
    }

    pub fn into_native(self) -> ProgramValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(term) => {
                if matches!(term.node(), KernelTermNode::Call { .. }) {
                    let KernelType::Program(ty) = term.ty() else {
                        unreachable!()
                    };
                    let format = MachineIntegerType::from_program_type(*ty)
                        .expect("machine call result type");
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
    pub fn native(&self) -> std::borrow::Cow<'_, ProgramValue> {
        match self {
            Self::Native(value) => std::borrow::Cow::Borrowed(value),
            Self::Shared(_) => std::borrow::Cow::Owned(self.clone().into_native()),
        }
    }
    pub fn program_type(&self) -> ProgramType {
        match self {
            Self::Native(value) => value.program_type(),
            Self::Shared(term) => match term.ty() {
                KernelType::Program(ty) => *ty,
                _ => unreachable!(),
            },
        }
    }
    pub(in crate::kernel) fn machine(
        &self,
    ) -> Option<(MachineIntegerType, MachineOperandView<'_>)> {
        let format = MachineIntegerType::from_program_type(self.program_type())?;
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

impl<V> ExpressionPath<V> {
    pub(in crate::kernel) fn map_value<W>(self, map: impl FnOnce(V) -> W) -> ExpressionPath<W> {
        ExpressionPath {
            outcome: self.outcome.map_value(map),
            facts: self.facts,
            obligations: self.obligations,
        }
    }
}

impl ExpressionPath<ExecutionValue> {
    pub(in crate::kernel) fn into_native(self) -> ExpressionPath {
        self.map_value(ExecutionValue::into_native)
    }
}

impl From<ExpressionPath> for ExpressionPath<ExecutionValue> {
    fn from(path: ExpressionPath) -> Self {
        path.map_value(ExecutionValue::retain_native)
    }
}

/// A local or outcome value keeps its exact producer payload. Stored identity observes the
/// same native machine key across native and retained storage representations;
/// specification producer equality remains exact on ExecutionValue itself.
#[derive(Clone, Debug)]
pub struct StoredExecutionValue(std::sync::Arc<StoredValueData>);
#[derive(Debug)]
struct StoredValueData {
    value: ExecutionValue,
    identity: std::sync::OnceLock<Option<SharedMachineIntegerTerm>>,
}
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd)]
enum StoredIdentity<'a> {
    Machine(&'a SharedMachineIntegerTerm),
    Native(&'a ProgramValue),
}
impl StoredExecutionValue {
    fn identity(&self) -> StoredIdentity<'_> {
        match self.0.identity.get_or_init(|| match &self.0.value {
            ExecutionValue::Shared(root) => Some(
                SharedMachineIntegerTerm::observe_shared(
                    MachineIntegerType::from_program_type(self.program_type())
                        .expect("machine storage"),
                    root.clone(),
                )
                .expect("retained machine storage"),
            ),
            ExecutionValue::Native(value) => {
                let (crate::kernel::integer_c_value!(term)) = value else {
                    return None;
                };
                Some(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::from_program_type(value.program_type()).unwrap(),
                    term.clone(),
                ))
            }
        }) {
            Some(identity) => StoredIdentity::Machine(identity),
            None => StoredIdentity::Native(self.native_payload().expect("native storage")),
        }
    }
    pub fn matches_native(&self, value: &ProgramValue) -> bool {
        self == &Self::from(value.clone())
    }
    pub fn into_value(self) -> ExecutionValue {
        match std::sync::Arc::try_unwrap(self.0) {
            Ok(data) => data.value,
            Err(data) => data.value.clone(),
        }
    }
    pub fn into_native(self) -> ProgramValue {
        self.into_value().into_native()
    }
}
impl std::ops::Deref for StoredExecutionValue {
    type Target = ExecutionValue;
    fn deref(&self) -> &Self::Target {
        &self.0.value
    }
}
impl From<ExecutionValue> for StoredExecutionValue {
    fn from(value: ExecutionValue) -> Self {
        let value = if value
            .shared()
            .is_some_and(|root| !root.is_shared_machine_operand())
        {
            ExecutionValue::Native(value.into_native())
        } else {
            value
        };
        Self(std::sync::Arc::new(StoredValueData {
            value,
            identity: Default::default(),
        }))
    }
}
impl From<ProgramValue> for StoredExecutionValue {
    fn from(value: ProgramValue) -> Self {
        ExecutionValue::from(value).into()
    }
}
impl From<StoredExecutionValue> for ExecutionValue {
    fn from(value: StoredExecutionValue) -> Self {
        value.into_value()
    }
}
impl PartialEq for StoredExecutionValue {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}
impl Eq for StoredExecutionValue {}
impl std::hash::Hash for StoredExecutionValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.identity(), state);
    }
}
impl PartialOrd for StoredExecutionValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredExecutionValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.identity().cmp(&other.identity())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_storage_identity_matches_native_without_changing_producer_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let term = MachineTerm::machine_binary(
            MachineIntegerType::UInt32,
            MachineBinaryOp::Multiply,
            MachineTerm::Variable(Variable(998320)),
            MachineTerm::uint32_constant(3),
        );
        let native = ExecutionValue::from(ProgramValue::UInt32(term.clone()));
        let root = KernelTermImport::default().machine(MachineIntegerType::UInt32, &term);
        let shared = ExecutionValue::from(root.clone());
        assert_ne!(native, shared, "producer equality stays exact");
        let exports = KernelTermExport::machine_export_count();
        let native = StoredExecutionValue::from(native);
        let shared = StoredExecutionValue::from(shared);
        assert_eq!(native, shared);
        assert_eq!(native.cmp(&shared), std::cmp::Ordering::Equal);
        let hash = |value: &StoredExecutionValue| {
            use std::hash::{Hash, Hasher};
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hash);
            hash.finish()
        };
        assert_eq!(hash(&native), hash(&shared));
        assert_eq!(shared.shared(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn execution_outcomes_preserve_native_values_and_refusals() {
        let value = ProgramValue::Int32(MachineTerm::constant(7));
        let outcome = ExpressionOutcome::Value(value.clone()).map_value(ExecutionValue::from);
        assert_eq!(
            outcome.map_value(ExecutionValue::into_native),
            ExpressionOutcome::Value(value)
        );
        let undefined =
            ExpressionOutcome::<ProgramValue>::UndefinedBehavior(UndefinedBehavior::SignedOverflow);
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
