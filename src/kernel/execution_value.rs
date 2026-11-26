//! Values retained between evaluation and execution boundaries.
//! Compatibility reads are explicit; a shared value owns only its common root.
use super::prelude::*;
pub(in crate::kernel) mod storage_keys;
use storage_keys::ProgramStorageKey;

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
                    || (matches!(a.ty(), KernelType::Algebraic(_))
                        && a.ty() == b.ty()
                        && a.algebraic_syntax_equal(b))
                    || matches!((FloatOperandView::from_shared(a), FloatOperandView::from_shared(b)), (Some(a), Some(b)) if a.syntax_equal(b))
                    || (a.ty() == &KernelType::Bool
                        && b.ty() == &KernelType::Bool
                        && BooleanOperandView::Shared(a)
                            .syntax_equal(BooleanOperandView::Shared(b)))
                    || matches!((a.pointer_payload(), b.pointer_payload()),
                        (Some(a), Some(b)) if a.same_source_payload(b))
                    || match (a.old_pointer_value(), b.old_pointer_value()) {
                        (Some(a), Some(b)) => a == b,
                        _ => false,
                    }
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
            Self::Shared(root) => root
                .old_pointer_value()
                .or_else(|| root.old_boolean_value())
                .or_else(|| {
                    matches!(root.node(), KernelTermNode::Variable(_))
                        .then(|| root.algebraic_native_value())
                        .flatten()
                }),
        }
    }
    pub fn pointer(&self) -> Option<&OldPointer> {
        let value = match self {
            Self::Native(value) => value,
            Self::Shared(root) => root.old_pointer_value()?,
        };
        match value {
            ProgramValue::Pointer(pointer) => Some(pointer),
            _ => None,
        }
    }
    pub fn byte_width(&self) -> u32 {
        self.program_type().byte_width()
    }
    /// Retain supported numeric, algebraic and producer-defined pointer reads
    /// at their execution boundary, preserving exact payload syntax.
    pub(in crate::kernel) fn retain_native(value: ProgramValue) -> Self {
        if let Some(view) = FloatOperandView::from_value(&value) {
            return KernelTermImport::default()
                .float(view.format(), view.old_form().expect("native float"))
                .into();
        }
        if let ProgramValue::Parameter(term) = &value {
            return KernelTermImport::default().algebraic(term).into();
        }
        if let ProgramValue::Pointer(pointer) = &value
            && let Some(root) = KernelTerm::retained_pointer_read(pointer)
        {
            return Self::Shared(root);
        }
        if let crate::kernel::integer_c_value!(term) = &value {
            // Scalar leaves have no expression prefix to retain. Keep their
            // existing cheap reading, including condition truth values.
            if matches!(
                term,
                OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_)
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

    /// Admit a completed address formation or cast. Load roots keep their
    /// definitions; other pointer producers are activated by their own slices.
    pub(in crate::kernel) fn retain_formed_pointer(value: ProgramValue) -> Self {
        let value = Self::retain_native(value);
        match value {
            Self::Native(ProgramValue::Pointer(pointer)) => {
                KernelTerm::shared_pointer_value(SharedPointer::import_produced(&pointer)).into()
            }
            value => value,
        }
    }

    /// A branch handoff retains an existing producer root or admits its
    /// selected complete pointer value without changing any other carrier.
    pub(in crate::kernel) fn retain_pointer_result(self) -> Self {
        match self {
            Self::Native(value @ ProgramValue::Pointer(_)) => Self::retain_formed_pointer(value),
            value => value,
        }
    }

    pub(in crate::kernel) fn with_pointer_binding(self, program_type: ProgramType) -> Self {
        if let Self::Shared(root) = &self
            && let Some(pointer) = root.pointer_payload()
        {
            return root
                .with_pointer_payload(pointer.with_binding_type(program_type))
                .into();
        }
        Self::retain_formed_pointer(self.into_native().retag_pointer(program_type))
    }

    /// Preserve the selected producer after an existing native conversion or
    /// entry-metadata operation. A changed address/type forms a new value.
    pub(in crate::kernel) fn retain_checked_pointer(&self, value: ProgramValue) -> Self {
        if let (Some(root), ProgramValue::Pointer(pointer)) = (self.shared(), &value) {
            return root.refined_pointer_argument(pointer).into();
        }
        if value.program_type().is_pointer() {
            Self::retain_formed_pointer(value)
        } else {
            Self::Native(value).retain_float_result()
        }
    }

    /// Same-type Boolean, algebraic and float coercions keep their source root.
    /// Other conversions retain the newly formed result.
    pub(in crate::kernel) fn retain_coerced_argument(&self, value: ProgramValue) -> Self {
        if self.shared().is_some_and(|root| {
            root.ty() == &KernelType::Bool
                || matches!(root.ty(), KernelType::Algebraic(_))
                || FloatOperandView::from_shared(root).is_some()
        }) && self.program_type() == value.program_type()
        {
            self.clone()
        } else {
            self.retain_checked_pointer(value)
        }
    }

    /// Retain one selected operand before crossing a native checking boundary.
    pub(in crate::kernel) fn common_operand(&self) -> KernelTerm {
        match self {
            Self::Shared(root) => root.clone(),
            Self::Native(ProgramValue::Pointer(pointer)) => {
                KernelTerm::retained_pointer_read(pointer).unwrap_or_else(|| {
                    KernelTerm::shared_pointer_value(SharedPointer::import_produced(pointer))
                })
            }
            Self::Native(value) => {
                KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()))
            }
        }
    }

    /// Read the logical truth carried by a Bool value. Raw C words keep the
    /// existing nonzero test; already logical roots remain shared.
    pub(in crate::kernel) fn boolean(&self) -> Option<KernelTerm> {
        match self {
            Self::Shared(root) if root.ty() == &KernelType::Bool => Some(root.clone()),
            Self::Native(ProgramValue::Bool(word)) => Some(
                KernelTermImport::default().condition(&OldConditionTerm::truth_of_bool_word(word)),
            ),
            _ => None,
        }
    }

    pub(in crate::kernel) fn algebraic(&self) -> Option<KernelTerm> {
        match self {
            Self::Shared(root)
                if matches!(root.node(), KernelTermNode::ProgramParameter { .. }) =>
            {
                let KernelTermNode::ProgramParameter { operand } = root.node() else {
                    unreachable!()
                };
                Some(operand.clone())
            }
            Self::Shared(root) if matches!(root.ty(), KernelType::Algebraic(_)) => {
                Some(root.clone())
            }
            Self::Native(ProgramValue::Parameter(value)) => {
                Some(KernelTermImport::default().algebraic(value))
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn float(&self) -> Option<FloatOperandView<'_>> {
        match self {
            Self::Shared(root) => FloatOperandView::from_shared(root),
            Self::Native(value) => FloatOperandView::from_value(value),
        }
    }

    /// Retain only the argument importer's exact logical Boolean carriers.
    /// Raw C words, widths and variable carriers retain their native spelling.
    pub(in crate::kernel) fn retain_boolean_result(self) -> Self {
        let Self::Native(ProgramValue::Bool(_)) = &self else {
            return self;
        };
        let root = self.common_operand();
        if root.ty() == &KernelType::Bool {
            Self::Shared(root)
        } else {
            self
        }
    }

    pub(in crate::kernel) fn retain_float_result(self) -> Self {
        match self {
            Self::Native(value) if FloatOperandView::from_value(&value).is_some() => {
                Self::retain_native(value)
            }
            value => value,
        }
    }

    pub(in crate::kernel) fn retain_algebraic_result(self) -> Self {
        match self {
            Self::Native(ProgramValue::Parameter(value)) => {
                KernelTermImport::default().algebraic(&value).into()
            }
            value => value,
        }
    }

    pub fn into_native(self) -> ProgramValue {
        match self {
            Self::Native(value) => value,
            Self::Shared(term) => {
                if let Some(value) = term.algebraic_native_term() {
                    return ProgramValue::Parameter(Box::new(value.clone()));
                }
                if let Some(value) = term.old_boolean_value() {
                    return value.clone();
                }
                if let Some(value) = term.old_pointer_value() {
                    return value.clone();
                }
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
                KernelType::Bool => ProgramType::Bool,
                KernelType::Algebraic(ty) => ProgramType::Parameter(TypeParameterName::of(ty)),
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
                Some((format, MachineOperandView::Old(term)))
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

/// A memory cell retains its producer and native structural equality/order.
/// Shared family keys cache structural fingerprints instead of exporting an
/// enclosing native value.
#[derive(Clone)]
pub struct StoredMemoryValue(std::sync::Arc<StoredMemoryData>);
#[derive(Debug)]
struct StoredMemoryData {
    value: ExecutionValue,
    key: std::sync::OnceLock<ProgramStorageKey>,
}
impl std::fmt::Debug for StoredMemoryValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self.native(), f)
    }
}
impl StoredMemoryValue {
    fn identity(&self) -> &ProgramStorageKey {
        self.0
            .key
            .get_or_init(|| ProgramStorageKey::for_value(&self.0.value))
    }
    fn same_retained_value(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0)
            || matches!((self.value().shared(), other.value().shared()), (Some(a), Some(b)) if a == b)
    }
    pub fn native(&self) -> &ProgramValue {
        match &self.0.value {
            ExecutionValue::Native(value) => value,
            ExecutionValue::Shared(root) => root
                .program_value_native_compat()
                .expect("native cell output"),
        }
    }
    pub(crate) fn value(&self) -> &ExecutionValue {
        &self.0.value
    }
    pub(crate) fn with_native_value(&self, value: ProgramValue) -> Self {
        if self.value().shared().is_some() {
            self.value().retain_checked_pointer(value).into()
        } else {
            value.into()
        }
    }
    pub(crate) fn into_value(self) -> ExecutionValue {
        match std::sync::Arc::try_unwrap(self.0) {
            Ok(data) => data.value,
            Err(data) => data.value.clone(),
        }
    }
    pub(crate) fn into_native(self) -> ProgramValue {
        self.into_value().into_native()
    }
    pub(crate) fn program_type(&self) -> ProgramType {
        self.0.value.program_type()
    }
    pub(crate) fn byte_width(&self) -> u32 {
        self.0.value.byte_width()
    }
}
impl From<ProgramValue> for StoredMemoryValue {
    fn from(value: ProgramValue) -> Self {
        Self::from(ExecutionValue::Native(value))
    }
}
impl From<ExecutionValue> for StoredMemoryValue {
    fn from(value: ExecutionValue) -> Self {
        let value = if value.shared().is_some_and(|root| {
            root.pointer_payload().is_none()
                && !root.is_shared_machine_operand()
                && root.ty() != &KernelType::Bool
                && !matches!(root.ty(), KernelType::Algebraic(_))
                && FloatOperandView::from_shared(root).is_none()
        }) {
            value.into_native().into()
        } else {
            value
        };
        Self(std::sync::Arc::new(StoredMemoryData {
            value,
            key: Default::default(),
        }))
    }
}
impl PartialEq for StoredMemoryValue {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for StoredMemoryValue {}
impl std::hash::Hash for StoredMemoryValue {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Native scalar cells can be visited for the first time while a
        // memory view is hashed. Keep their existing one-word identity.
        if let ExecutionValue::Native(value @ (crate::kernel::integer_c_value!(word))) =
            self.value()
            && matches!(
                word,
                OldMachineTerm::Constant { .. }
                    | OldMachineTerm::Variable(_)
                    | OldMachineTerm::MemoryLoad(..)
                    | OldMachineTerm::ThreadHandle(_)
            )
        {
            return std::hash::Hash::hash(value, state);
        }
        match self.identity() {
            ProgramStorageKey::Native(value) => std::hash::Hash::hash(value, state),
            ProgramStorageKey::Scalar(ty, key)
                if let Some(format) = MachineIntegerType::from_program_type(*ty)
                    && let Some(word) = key.native_atom() =>
            {
                let value = crate::kernel::wrap_exact_machine_value(format, word.clone());
                std::hash::Hash::hash(&value, state);
            }
            key => std::hash::Hash::hash(&key, state),
        }
    }
}
impl PartialOrd for StoredMemoryValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredMemoryValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.same_retained_value(other) {
            return std::cmp::Ordering::Equal;
        }
        if let (ExecutionValue::Native(left), ExecutionValue::Native(right)) =
            (self.value(), other.value())
        {
            return left.cmp(right);
        }
        self.identity().cmp(other.identity())
    }
}
impl PartialEq<ProgramValue> for StoredMemoryValue {
    fn eq(&self, other: &ProgramValue) -> bool {
        match self.value() {
            ExecutionValue::Native(value) => value == other,
            ExecutionValue::Shared(_) => &ProgramStorageKey::native(other) == self.identity(),
        }
    }
}
impl PartialEq<StoredMemoryValue> for ProgramValue {
    fn eq(&self, other: &StoredMemoryValue) -> bool {
        other == self
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
    identity: std::sync::OnceLock<StoredKey>,
}
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd)]
enum StoredIdentity<'a> {
    Machine(&'a SharedMachineIntegerTerm),
    Native(&'a ProgramStorageKey),
}
/// Local machine identity retains numeric observation handles. Other values
/// use the exact storage identity shared with memory cells.
#[derive(Debug)]
enum StoredKey {
    Machine(SharedMachineIntegerTerm),
    Native(ProgramStorageKey),
}

impl StoredKey {
    fn for_value(value: &ExecutionValue) -> Self {
        if let Some(root) = value.algebraic() {
            return Self::Native(ProgramStorageKey::Algebraic(
                storage_keys::algebraic_for_root(&root),
            ));
        }
        let Some((format, view)) = value.machine() else {
            return Self::Native(ProgramStorageKey::for_value(value));
        };
        Self::Machine(match view {
            MachineOperandView::Shared(root) => {
                SharedMachineIntegerTerm::observe_shared(format, root.clone())
                    .expect("retained machine storage")
            }
            MachineOperandView::Old(term) => SharedMachineIntegerTerm::intern(format, term.clone()),
        })
    }
}

impl StoredExecutionValue {
    pub(crate) fn same_retained_root(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0)
            || matches!((self.shared(), other.shared()), (Some(a), Some(b)) if a == b)
    }
    fn identity(&self) -> StoredIdentity<'_> {
        match self
            .0
            .identity
            .get_or_init(|| StoredKey::for_value(&self.0.value))
        {
            StoredKey::Machine(identity) => StoredIdentity::Machine(identity),
            StoredKey::Native(key) => StoredIdentity::Native(key),
        }
    }
    /// Preserve an exact native-payload comparison at a compatibility consumer.
    /// Storage equality can identify different machine spellings of one word;
    /// an outcome refresh must retain the earlier, stricter payload contract.
    pub(crate) fn same_native_value(&self, other: &Self) -> bool {
        if let (ExecutionValue::Native(left), ExecutionValue::Native(right)) =
            (&self.0.value, &other.0.value)
        {
            return left == right;
        }
        self.same_retained_root(other)
            || ProgramStorageKey::for_value(self) == ProgramStorageKey::for_value(other)
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
        let value = if value.shared().is_some_and(|root| {
            !root.is_shared_machine_operand()
                && root.pointer_payload().is_none()
                && root.ty() != &KernelType::Bool
                && !matches!(root.ty(), KernelType::Algebraic(_))
                && FloatOperandView::from_shared(root).is_none()
        }) {
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
        self.same_retained_root(other) || self.identity() == other.identity()
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
        if self.same_retained_root(other) {
            std::cmp::Ordering::Equal
        } else {
            self.identity().cmp(&other.identity())
        }
    }
}

#[cfg(test)]
mod storage_contract_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_storage_preserves_roots_and_native_key_contracts() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = TypeParameterName::intern("StoredAlgebraicT").algebraic_type();
        let roots = [
            KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(999764)),
            KernelTerm::algebraic_read(
                ty.clone(),
                crate::kernel::ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
                SharedAddress::import(&OldAddress::symbolic(Variable(999765))),
            ),
        ];
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut hasher);
            hasher.finish()
        }
        for root in roots {
            let value = ExecutionValue::Shared(root.clone());
            let native = value.clone().into_native();
            let stored = StoredExecutionValue::from(value.clone());
            let expected = StoredExecutionValue::from(native.clone());
            assert_eq!(stored, expected);
            assert_eq!(stored.cmp(&expected), std::cmp::Ordering::Equal);
            assert_eq!(hash(&stored), hash(&expected));
            assert_eq!(stored.clone().into_value().shared(), Some(&root));
            assert_eq!(
                value.retain_coerced_argument(native.clone()).shared(),
                Some(&root)
            );
            let cell = StoredMemoryValue::from(value);
            assert_eq!(cell.native(), &native);
            assert_eq!(hash(&cell), hash(&StoredMemoryValue::from(native.clone())));
            assert_eq!(cell.into_value().shared(), Some(&root));
        }
    }
    #[test]
    fn boolean_storage_preserves_roots_and_native_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = KernelTerm::variable(KernelType::Bool, Variable(999500));
        let roots = [
            KernelTermImport::default().condition(&OldConditionTerm::Constant(false)),
            variable.clone(),
            KernelTerm::boolean_if([
                variable.clone(),
                KernelTerm::variable(KernelType::Bool, Variable(999501)),
                KernelTermImport::default().condition(&OldConditionTerm::Constant(true)),
            ]),
            KernelTermImport::default()
                .boolean_call(&SharedPureApplication::intern("stored_bool".into(), vec![])),
        ];
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut h = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut h);
            h.finish()
        }
        for root in roots {
            let native = ExecutionValue::Shared(root.clone()).into_native();
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let native_stored = StoredExecutionValue::from(native.clone());
            assert_eq!(stored, native_stored);
            assert_eq!(hash(&stored), hash(&native_stored));
            assert_eq!(stored.clone().into_value().shared(), Some(&root));
            assert_eq!(stored.into_value().shared(), Some(&root));
            let cell = StoredMemoryValue::from(ExecutionValue::Shared(root.clone()));
            assert_eq!(cell.native(), &native);
            assert_eq!(hash(&cell), hash(&StoredMemoryValue::from(native.clone())));
            for other in [
                ProgramValue::Void,
                ProgramValue::Bool(OldMachineTerm::Constant {
                    format: MachineIntegerType::UInt8,
                    bits: 2,
                }),
                native.clone(),
            ] {
                assert_eq!(
                    cell.cmp(&StoredMemoryValue::from(other.clone())),
                    native.cmp(&other)
                );
                assert_eq!(
                    StoredExecutionValue::from(ExecutionValue::Shared(root.clone()))
                        .cmp(&StoredExecutionValue::from(other.clone())),
                    native_stored.cmp(&StoredExecutionValue::from(other))
                );
            }
            let address = SymbolicMemory::local_pointer("stored_bool");
            let memory = SymbolicMemory::new()
                .with_block(address.base.clone(), 1)
                .store_retained(address.clone(), cell.into_value());
            assert_eq!(
                memory.known_retained_value(&address).unwrap().shared(),
                Some(&root)
            );
            assert_eq!(memory.known_value(&address), Some(native));
            assert!(std::ptr::eq(
                root.old_boolean_value().unwrap(),
                root.old_boolean_value().unwrap()
            ));
        }
        let raw = ProgramValue::Bool(OldMachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        });
        let cell = StoredMemoryValue::from(raw.clone());
        assert_eq!(cell.native(), &raw);
        assert!(cell.value().shared().is_none());
    }

    #[test]
    fn exact_native_value_comparison_does_not_use_machine_storage_equivalence() {
        let _session = crate::kernel::VerificationSession::enter();
        let argument = OldMachineTerm::Variable(Variable(998319));
        let call = |argument| {
            ProgramValue::UInt32(OldMachineTerm::ClickFunctionApplication {
                name: "payload_identity".into(),
                arguments: vec![argument],
            })
        };
        let native_argument = call(PureFunctionArgument::Value(ProgramValue::UInt32(
            argument.clone(),
        )));
        let shared_argument = call(PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, argument),
        ));
        assert_ne!(native_argument, shared_argument);
        let native = StoredExecutionValue::from(native_argument.clone());
        let retained = StoredExecutionValue::from(shared_argument.clone());
        assert_eq!(
            native, retained,
            "storage observes the same typed call argument"
        );
        assert!(
            !native.same_native_value(&retained),
            "refresh keeps exact native payloads"
        );
        assert!(!retained.same_native_value(&native));
        assert!(native.same_native_value(&native.clone()));
        let ProgramValue::UInt32(term) = &native_argument else {
            unreachable!()
        };
        let root = KernelTermImport::default().machine(MachineIntegerType::UInt32, term);
        let shared = StoredExecutionValue::from(ExecutionValue::Shared(root));
        let exported = shared.clone().into_native();
        for (stored, native) in [(native, native_argument), (retained, shared_argument)] {
            assert_eq!(shared.same_native_value(&stored), exported == native);
            assert_eq!(stored.same_native_value(&shared), native == exported);
        }
    }

    #[test]
    fn local_storage_identity_matches_native_without_changing_producer_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let term = OldMachineTerm::machine_binary(
            MachineIntegerType::UInt32,
            MachineBinaryOp::Multiply,
            OldMachineTerm::Variable(Variable(998320)),
            OldMachineTerm::uint32_constant(3),
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
    fn pointer_local_storage_retains_root_and_native_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = OldPointer::new(
            OldAddress::symbolic(Variable(1027000)),
            ProgramType::Int32Pointer,
        );
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "local_source".into(),
                vec![],
            ),
            SharedPointer::import(&pointer),
        );
        let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        let native = StoredExecutionValue::from(ProgramValue::Pointer(pointer.clone()));
        assert_eq!(stored, native);
        assert_eq!(stored.cmp(&native), std::cmp::Ordering::Equal);
        let hash = |value: &StoredExecutionValue| {
            use std::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(&stored), hash(&native));
        assert_eq!(stored.shared(), Some(&root));
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "p",
            stored,
            ProgramType::Int32Pointer,
            false,
            false,
            false,
            false,
        );
        assert_eq!(state.locals.get("p").unwrap().shared(), Some(&root));
        {
            let value = ExecutionValue::Shared(root.clone())
                .with_pointer_binding(ProgramType::Int32Pointer);
            assert!(matches!(
                value.shared().unwrap().node(),
                KernelTermNode::PointerCall { .. }
            ));
            let expected = pointer.clone();
            assert!(
                value
                    .shared()
                    .unwrap()
                    .pointer_payload()
                    .unwrap()
                    .same_source_payload(&SharedPointer::import(&expected))
            );
        }
        let retagged = ExecutionValue::Shared(root).with_pointer_binding(ProgramType::VoidPointer);
        assert_eq!(retagged.program_type(), ProgramType::VoidPointer);
        assert!(matches!(
            retagged.shared().unwrap().node(),
            KernelTermNode::Pointer { .. }
        ));
    }

    #[test]
    fn pointer_memory_cells_keep_roots_and_the_previous_native_key() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = OldPointer::new(
            OldAddress::symbolic(Variable(1027500)),
            ProgramType::Int32Pointer,
        );
        let native = ProgramValue::Pointer(pointer.clone());
        let root = KernelTerm::shared_pointer_value(SharedPointer::import(&pointer));
        let retained = StoredMemoryValue::from(ExecutionValue::Shared(root.clone()));
        let native_cell = StoredMemoryValue::from(native.clone());
        assert_eq!(retained, native_cell);
        assert_eq!(retained.cmp(&native_cell), std::cmp::Ordering::Equal);
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut hash);
            hash.finish()
        }
        assert_eq!(hash(&retained), hash(&native_cell));
        assert_eq!(format!("{retained:?}"), format!("{native:?}"));
        let address = OldAddress::symbolic(Variable(1027501));
        let mut cells = CellStore::new();
        cells.insert_retained(address.clone(), retained);
        assert_eq!(cells.get_retained(&address).unwrap().shared(), Some(&root));
        assert_eq!(cells.get(&address), Some(native.clone()));
        assert_eq!(cells.iter().next().unwrap().1, &native);
    }

    #[test]
    fn pointer_store_history_keeps_the_root_after_cache_forgetting() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = SymbolicMemory::local_pointer("retained_pointer_cell");
        let pointer = OldPointer::new(
            OldAddress::symbolic(Variable(1027600)),
            ProgramType::Int32Pointer,
        );
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "stored_source".into(),
                vec![],
            ),
            SharedPointer::import(&pointer),
        );
        let memory = SymbolicMemory::new()
            .with_block(address.base.clone(), C_POINTER_BYTE_WIDTH)
            .store_retained(address.clone(), ExecutionValue::Shared(root.clone()));
        assert_eq!(
            memory.known_retained_value(&address).unwrap().shared(),
            Some(&root)
        );
        let forgotten = memory.without_possible_aliasing_cells(
            &address.offset_by_bytes(1),
            1,
            &PureFactContext::new(),
        );
        assert!(forgotten.known_value(&address).is_none());
        for retained_state in [&memory, &forgotten] {
            let origin = OldAddress::loaded_value(
                &crate::kernel::intern_memory_ref(retained_state),
                &address,
            );
            let recovered =
                crate::kernel::memory_history::complete_pointer_carrier_read_retained_value(
                    &origin,
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(recovered.shared(), Some(&root));
            let paths = crate::kernel::eval::evaluate_retained_memory_load_paths(
                &crate::kernel::ProgramPoint::of_memory(retained_state),
                address.clone(),
                ProgramType::Int32Pointer,
                ExecutionFacts::new(),
                vec![],
                &PureFactContext::new(),
                false,
                false,
                None,
                None,
                false,
            );
            assert_eq!(paths.len(), 1);
            let ExpressionOutcome::Value(loaded) = &paths[0].outcome else {
                panic!("retained pointer load: {:?}", paths[0].outcome);
            };
            assert_eq!(loaded.shared(), Some(&root));
        }
    }

    #[test]
    fn execution_outcomes_preserve_native_values_and_refusals() {
        let value = ProgramValue::Int32(OldMachineTerm::constant(7));
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

#[cfg(test)]
mod float_handoff_tests {
    use super::*;
    #[test]
    fn float_execution_storage_retains_roots_and_exact_native_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(value, &mut hash);
            hash.finish()
        }
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let roots = [
                KernelTerm::float_call(format, "stored_float".into(), vec![]),
                KernelTermImport::default().float(
                    format,
                    &match format {
                        KernelFloatType::Float32 => OldMachineTerm::uint32_constant(0x7fc00123),
                        KernelFloatType::Float64 => {
                            OldMachineTerm::uint64_constant(0x8000000000000000)
                        }
                    },
                ),
            ];
            for root in roots {
                let source = ExecutionValue::Shared(root.clone());
                let native = source.clone().into_native();
                let exports = KernelTermExport::float_export_count();
                let stored = StoredExecutionValue::from(source.clone());
                assert_eq!(stored.shared(), Some(&root));
                assert_eq!(stored.clone().into_value().shared(), Some(&root));
                assert_eq!(
                    source.retain_coerced_argument(native.clone()).shared(),
                    Some(&root)
                );
                assert_eq!(KernelTermExport::float_export_count(), exports);
                let expected = StoredExecutionValue::from(native.clone());
                assert_eq!(stored, expected);
                assert_eq!(stored.cmp(&expected), std::cmp::Ordering::Equal);
                assert_eq!(hash(&stored), hash(&expected));
                assert_eq!(ExecutionValue::retain_native(native).shared(), Some(&root));
            }
        }
    }
}

#[cfg(test)]
mod float_cell_key_tests {
    use super::*;
    #[test]
    fn float_memory_keys_match_native_bits_and_ordering() {
        let _session = crate::kernel::VerificationSession::enter();
        fn hash(value: &impl std::hash::Hash) -> u64 {
            use std::hash::Hasher;
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            value.hash(&mut hasher);
            hasher.finish()
        }
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let roots = [
                KernelTerm::float_call(format, "float_cell_key".into(), vec![]),
                KernelTermImport::default().float(
                    format,
                    &match format {
                        KernelFloatType::Float32 => OldMachineTerm::uint32_constant(0x7fc00123),
                        KernelFloatType::Float64 => {
                            OldMachineTerm::uint64_constant(0x8000000000000000)
                        }
                    },
                ),
            ];
            for root in roots {
                let value = ExecutionValue::Shared(root.clone());
                let native = value.clone().into_native();
                let cell = StoredMemoryValue::from(value);
                assert_eq!(cell.value().shared(), Some(&root));
                assert_eq!(cell.native(), &native);
                assert_eq!(hash(&cell), hash(&StoredMemoryValue::from(native.clone())));
                for other in [
                    ProgramValue::Void,
                    native.clone(),
                    ProgramValue::Float64(OldMachineTerm::uint64_constant(0)),
                ] {
                    let expected = native.cmp(&other);
                    let other = StoredMemoryValue::from(other);
                    assert_eq!(cell.cmp(&other), expected);
                    assert_eq!(cell == other, expected == std::cmp::Ordering::Equal);
                }
                assert_eq!(cell.into_value().shared(), Some(&root));
            }
        }
    }
}

/// Immutable program-value storage. Native inputs remain explicit compatibility
/// inputs; producer roots survive every clone and handoff without exporting.
/// Equality follows native syntax, separately from execution observation keys.
#[derive(Clone, Debug)]
pub(crate) struct RetainedProgramValue(std::sync::Arc<RetainedProgramData>);

#[derive(Debug)]
struct RetainedProgramData {
    value: ExecutionValue,
    key: std::sync::OnceLock<ProgramStorageKey>,
}

impl From<ProgramValue> for RetainedProgramValue {
    fn from(value: ProgramValue) -> Self {
        Self::from(ExecutionValue::Native(value))
    }
}
impl From<ExecutionValue> for RetainedProgramValue {
    fn from(value: ExecutionValue) -> Self {
        Self(std::sync::Arc::new(RetainedProgramData {
            value,
            key: Default::default(),
        }))
    }
}
impl RetainedProgramValue {
    pub(crate) fn value(&self) -> &ExecutionValue {
        &self.0.value
    }

    pub(crate) fn program_type(&self) -> ProgramType {
        self.value().program_type()
    }

    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        self.value().shared()
    }

    pub(in crate::kernel) fn storage_key(&self) -> &ProgramStorageKey {
        self.0
            .key
            .get_or_init(|| ProgramStorageKey::for_value(self.value()))
    }

    pub(in crate::kernel) fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.value(), other.value()) {
            (ExecutionValue::Native(left), ExecutionValue::Native(right)) => left.cmp(right),
            (ExecutionValue::Shared(left), ExecutionValue::Shared(right)) if left == right => {
                std::cmp::Ordering::Equal
            }
            _ => self.storage_key().cmp(other.storage_key()),
        }
    }

    pub(crate) fn old_form(&self) -> &ProgramValue {
        match self.value() {
            ExecutionValue::Native(value) => value,
            ExecutionValue::Shared(root) => root
                .program_value_native_compat()
                .expect("stored program value output"),
        }
    }
    pub(crate) fn into_native_compat(self) -> ProgramValue {
        self.into_value().into_native()
    }
    pub(crate) fn into_value(self) -> ExecutionValue {
        match std::sync::Arc::try_unwrap(self.0) {
            Ok(data) => data.value,
            Err(data) => data.value.clone(),
        }
    }
}
impl PartialEq for RetainedProgramValue {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0) || self.cmp(other).is_eq()
    }
}
impl Eq for RetainedProgramValue {}
