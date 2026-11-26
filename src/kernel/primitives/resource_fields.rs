//! Immutable resource fields. Producers keep their common roots;
//! native input lists and selected compatibility readers stay explicit.
use super::integer::IntegerShallowKey;
use super::*;
use crate::kernel::execution_value::storage_keys::{
    AlgebraicStorageKey, ProgramStorageKey, algebraic_for_root,
};
use crate::kernel::{ExecutionValue, RetainedProgramValue};
use std::borrow::Cow;

/// Borrowed native field output without allocating a second enclosing value.
/// Variant order follows `AlgebraicValue` for its existing identity contract.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFieldValue<'a> {
    Program(&'a ProgramValue),
    Integer(&'a IntegerTerm),
    Algebraic(&'a AlgebraicTerm),
}
impl<'a> From<&'a AlgebraicValue> for ResourceFieldValue<'a> {
    fn from(value: &'a AlgebraicValue) -> Self {
        match value {
            AlgebraicValue::Program(value) => Self::Program(value),
            AlgebraicValue::Integer(value) => Self::Integer(value),
            AlgebraicValue::Algebraic(value) => Self::Algebraic(value),
        }
    }
}
impl<'a> ResourceFieldValue<'a> {
    pub fn as_program_value(self) -> Option<&'a ProgramValue> {
        match self {
            Self::Program(value) => Some(value),
            _ => None,
        }
    }
    pub(crate) fn into_native(self) -> AlgebraicValue {
        match self {
            Self::Program(value) => AlgebraicValue::Program(value.clone()),
            Self::Integer(value) => AlgebraicValue::Integer(value.clone()),
            Self::Algebraic(value) => AlgebraicValue::Algebraic(value.clone()),
        }
    }
}

#[derive(Eq, PartialEq, Hash, Ord, PartialOrd)]
enum FieldKey {
    Program(ProgramStorageKey),
    Integer(IntegerShallowKey),
    Algebraic(AlgebraicStorageKey),
}

impl FieldKey {
    fn native(value: &AlgebraicValue) -> Self {
        match value {
            AlgebraicValue::Program(value) => Self::Program(ProgramStorageKey::native(value)),
            AlgebraicValue::Integer(value) => Self::Integer(value.shallow_key()),
            AlgebraicValue::Algebraic(value) => Self::Algebraic(AlgebraicStorageKey::native(value)),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum StoredResourceField {
    Input(AlgebraicValue),
    Program(RetainedProgramValue),
    Integer(KernelTerm),
    Algebraic(KernelTerm),
}
impl StoredResourceField {
    pub(crate) fn from_minted(value: AlgebraicValue) -> Self {
        match value {
            AlgebraicValue::Program(value) => {
                let root =
                    KernelTermImport::default().argument(&PureFunctionArgument::Value(value));
                Self::from_program(ExecutionValue::Shared(root))
            }
            AlgebraicValue::Integer(value) => {
                Self::Integer(KernelTermImport::for_exact_field_inputs().integer(&value.into()))
            }
            AlgebraicValue::Algebraic(value) => {
                Self::Algebraic(KernelTermImport::for_exact_field_inputs().algebraic(&value))
            }
        }
    }
    pub(crate) fn from_program(value: ExecutionValue) -> Self {
        match StoredExecutionValue::from(value).into_value() {
            ExecutionValue::Native(value) => Self::Input(AlgebraicValue::Program(value)),
            value => Self::Program(value.into()),
        }
    }
    fn key(&self) -> FieldKey {
        match self {
            Self::Input(value) => FieldKey::native(value),
            Self::Program(value) => FieldKey::Program(value.storage_key().clone()),
            Self::Integer(root) => {
                FieldKey::Integer(root.integer_exact_key().expect("Integer field"))
            }
            Self::Algebraic(root) => FieldKey::Algebraic(algebraic_for_root(root)),
        }
    }

    fn native(&self) -> ResourceFieldValue<'_> {
        match self {
            Self::Input(value) => value.into(),
            Self::Program(value) => ResourceFieldValue::Program(value.old_form()),
            Self::Integer(root) => {
                ResourceFieldValue::Integer(root.integer_native_compat().expect("Integer field"))
            }
            Self::Algebraic(root) => ResourceFieldValue::Algebraic(
                root.algebraic_native_term().expect("algebraic field"),
            ),
        }
    }
}

#[derive(Clone)]
pub struct ResourceFieldValues(Arc<FieldData>);
struct FieldData {
    values: FieldStorage,
    keys: std::sync::OnceLock<Box<[FieldKey]>>,
}
enum FieldStorage {
    Input(NativeResourceArguments),
    Retained(Box<[StoredResourceField]>),
}
impl AsRef<ResourceFieldValues> for ResourceFieldValues {
    fn as_ref(&self) -> &ResourceFieldValues {
        self
    }
}
impl Default for ResourceFieldValues {
    fn default() -> Self {
        Self::from(Vec::<AlgebraicValue>::new())
    }
}
impl ResourceFieldValues {
    pub fn len(&self) -> usize {
        match &self.0.values {
            FieldStorage::Input(values) => values.len(),
            FieldStorage::Retained(values) => values.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn get(&self, index: usize) -> Option<ResourceFieldValue<'_>> {
        match &self.0.values {
            FieldStorage::Input(values) => values.get(index).map(ResourceFieldValue::from),
            FieldStorage::Retained(values) => values.get(index).map(StoredResourceField::native),
        }
    }
    pub fn first(&self) -> Option<ResourceFieldValue<'_>> {
        self.get(0)
    }
    pub fn last(&self) -> Option<ResourceFieldValue<'_>> {
        self.len().checked_sub(1).and_then(|index| self.get(index))
    }
    pub(crate) fn fixed_values<const N: usize>(&self) -> Option<[ResourceFieldValue<'_>; N]> {
        (self.len() == N).then(|| std::array::from_fn(|index| self.get(index).unwrap()))
    }
    pub fn iter(&self) -> ResourceFieldIter<'_> {
        ResourceFieldIter {
            values: self,
            range: 0..self.len(),
        }
    }
    pub(crate) fn program_value(&self, index: usize) -> Option<ExecutionValue> {
        match &self.0.values {
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Program(value) => Some(value.clone().into_value()),
                StoredResourceField::Input(AlgebraicValue::Program(value)) => {
                    Some(value.clone().into())
                }
                _ => None,
            },
            FieldStorage::Input(values) => match values.get(index)? {
                AlgebraicValue::Program(value) => Some(value.clone().into()),
                _ => None,
            },
        }
    }
    pub(crate) fn stored_field(&self, index: usize) -> Option<StoredResourceField> {
        match &self.0.values {
            FieldStorage::Input(values) => {
                values.get(index).cloned().map(StoredResourceField::Input)
            }
            FieldStorage::Retained(values) => values.get(index).cloned(),
        }
    }
    pub(crate) fn from_stored(values: impl IntoIterator<Item = StoredResourceField>) -> Self {
        Self::new(FieldStorage::Retained(values.into_iter().collect()))
    }
    /// Values minted by the existing typed field producers. Native public
    /// inputs use `From<NativeResourceArguments>` and retain their admission checks.
    pub(crate) fn from_minted(values: Vec<AlgebraicValue>) -> Self {
        Self::from_stored(values.into_iter().map(StoredResourceField::from_minted))
    }
    pub(crate) fn retained_program(&self, index: usize) -> Option<&ExecutionValue> {
        match &self.0.values {
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Program(value) => Some(value.value()),
                _ => None,
            },
            _ => None,
        }
    }
    pub(crate) fn integer_term(&self, index: usize) -> Option<StoredIntegerTerm> {
        let value = match &self.0.values {
            FieldStorage::Input(values) => values.get(index)?,
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Integer(root) => {
                    return StoredIntegerTerm::from_root(root.clone());
                }
                StoredResourceField::Input(value) => value,
                _ => return None,
            },
        };
        match value {
            AlgebraicValue::Integer(value) => Some(value.clone().into()),
            _ => None,
        }
    }

    pub(crate) fn retained_integer(&self, index: usize) -> Option<&KernelTerm> {
        match &self.0.values {
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Integer(root) => Some(root),
                _ => None,
            },
            _ => None,
        }
    }
    pub(crate) fn retained_algebraic(&self, index: usize) -> Option<&KernelTerm> {
        match &self.0.values {
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Algebraic(root) => Some(root),
                _ => None,
            },
            _ => None,
        }
    }
    pub fn to_vec(&self) -> Vec<AlgebraicValue> {
        self.iter().map(ResourceFieldValue::into_native).collect()
    }
    /// Whole-list native APIs pay only for their explicitly selected output.
    /// There is no parallel cached native list beside the retained fields.
    pub(crate) fn native_values(&self) -> Cow<'_, [AlgebraicValue]> {
        match &self.0.values {
            FieldStorage::Input(values) => Cow::Borrowed(values),
            FieldStorage::Retained(_) => Cow::Owned(self.to_vec()),
        }
    }
    pub(crate) fn matches_schema(&self, schema: &ResourceFieldSchema) -> bool {
        if self.len() != schema.fields().len() {
            return false;
        }
        schema.fields().iter().enumerate().all(|(index, (_, ty))| {
            if let FieldStorage::Retained(values) = &self.0.values {
                // Retained values come from the existing typed producers. Raw
                // public inputs still take the native admission checks below.
                match &values[index] {
                    StoredResourceField::Program(value) => return matches!(ty, ResourceFieldType::Program(expected) if *expected == value.program_type()),
                    StoredResourceField::Integer(root) => return *ty == ResourceFieldType::Integer && root.ty() == &KernelType::Integer,
                    StoredResourceField::Algebraic(root) => return matches!((ty,root.ty()), (ResourceFieldType::Algebraic(expected),KernelType::Algebraic(actual)) if expected==actual),
                    StoredResourceField::Input(_) => {},
                }
            }
            match (ty, self.get(index).expect("field index")) {
                (ResourceFieldType::Integer, ResourceFieldValue::Integer(_)) => true,
                (ResourceFieldType::Program(ty), ResourceFieldValue::Program(value)) => *ty == value.program_type(),
                (ResourceFieldType::Algebraic(ty), ResourceFieldValue::Algebraic(value)) => *ty == value.algebraic_type && value.is_well_formed(),
                _ => false,
            }
        })
    }
    fn new(values: FieldStorage) -> Self {
        Self(Arc::new(FieldData {
            values,
            keys: Default::default(),
        }))
    }

    fn keys(&self) -> &[FieldKey] {
        self.0.keys.get_or_init(|| match &self.0.values {
            FieldStorage::Input(values) => values.iter().map(FieldKey::native).collect(),
            FieldStorage::Retained(values) => values.iter().map(StoredResourceField::key).collect(),
        })
    }

    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl From<NativeResourceArguments> for ResourceFieldValues {
    fn from(values: NativeResourceArguments) -> Self {
        Self::new(FieldStorage::Input(values))
    }
}
impl From<&[AlgebraicValue]> for ResourceFieldValues {
    fn from(values: &[AlgebraicValue]) -> Self {
        values.to_vec().into()
    }
}
impl From<Vec<AlgebraicValue>> for ResourceFieldValues {
    fn from(values: Vec<AlgebraicValue>) -> Self {
        NativeResourceArguments::from(values).into()
    }
}
impl<const N: usize> From<[AlgebraicValue; N]> for ResourceFieldValues {
    fn from(values: [AlgebraicValue; N]) -> Self {
        Vec::from(values).into()
    }
}
impl FromIterator<AlgebraicValue> for ResourceFieldValues {
    fn from_iter<T: IntoIterator<Item = AlgebraicValue>>(values: T) -> Self {
        values
            .into_iter()
            .collect::<NativeResourceArguments>()
            .into()
    }
}
impl std::fmt::Debug for ResourceFieldValues {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl PartialEq for ResourceFieldValues {
    fn eq(&self, other: &Self) -> bool {
        if self.shares_storage_with(other) {
            return true;
        }
        match (&self.0.values, &other.0.values) {
            (FieldStorage::Input(left), FieldStorage::Input(right)) => left == right,
            _ => self.len() == other.len() && self.keys() == other.keys(),
        }
    }
}
impl Eq for ResourceFieldValues {}
impl Ord for ResourceFieldValues {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.shares_storage_with(other) {
            return std::cmp::Ordering::Equal;
        }
        match (&self.0.values, &other.0.values) {
            (FieldStorage::Input(left), FieldStorage::Input(right)) => left.cmp(right),
            _ => self.keys().cmp(other.keys()),
        }
    }
}
impl PartialOrd for ResourceFieldValues {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Hash for ResourceFieldValues {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for key in self.keys() {
            key.hash(state);
        }
    }
}
impl PartialEq<[AlgebraicValue]> for ResourceFieldValues {
    fn eq(&self, other: &[AlgebraicValue]) -> bool {
        match &self.0.values {
            FieldStorage::Input(values) => values.as_ref() == other,
            _ => {
                self.len() == other.len()
                    && self
                        .keys()
                        .iter()
                        .zip(other)
                        .all(|(key, value)| *key == FieldKey::native(value))
            }
        }
    }
}
impl<const N: usize> PartialEq<[AlgebraicValue; N]> for ResourceFieldValues {
    fn eq(&self, other: &[AlgebraicValue; N]) -> bool {
        self == other.as_slice()
    }
}
impl PartialEq<Vec<AlgebraicValue>> for ResourceFieldValues {
    fn eq(&self, other: &Vec<AlgebraicValue>) -> bool {
        self == other.as_slice()
    }
}
impl PartialEq<NativeResourceArguments> for ResourceFieldValues {
    fn eq(&self, other: &NativeResourceArguments) -> bool {
        self == other.as_ref()
    }
}

impl From<&ResourceFieldValues> for ResourceFieldValues {
    fn from(values: &ResourceFieldValues) -> Self {
        values.clone()
    }
}
pub struct ResourceFieldIter<'a> {
    values: &'a ResourceFieldValues,
    range: std::ops::Range<usize>,
}
impl<'a> Iterator for ResourceFieldIter<'a> {
    type Item = ResourceFieldValue<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().and_then(|index| self.values.get(index))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}
impl DoubleEndedIterator for ResourceFieldIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range
            .next_back()
            .and_then(|index| self.values.get(index))
    }
}
impl ExactSizeIterator for ResourceFieldIter<'_> {}
impl<'a> IntoIterator for &'a ResourceFieldValues {
    type Item = ResourceFieldValue<'a>;
    type IntoIter = ResourceFieldIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a> From<&ResourceFieldValue<'a>> for ResourceFieldValue<'a> {
    fn from(value: &ResourceFieldValue<'a>) -> Self {
        *value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelType, MachineBinaryOp, MachineIntegerType, VerificationSession};

    fn schema(ty: ProgramType) -> ResourceFieldSchema {
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::Program(ty))]).unwrap()
    }
    fn instance(fields: ResourceFieldValues, ty: ProgramType) -> ResourceInstance {
        ResourceInstance::new(
            InstanceId::from_variable(Variable(10993301)),
            "FieldBox".into(),
            vec![].into(),
            schema(ty),
            fields,
        )
        .unwrap()
    }
    fn hash(value: &impl Hash) -> u64 {
        use std::hash::Hasher;
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn field_views_preserve_native_identity_order_hash_and_debug() {
        let _session = VerificationSession::enter();
        let word = OldMachineTerm::Variable(Variable(10993302));
        let call = |arg| {
            AlgebraicValue::Program(ProgramValue::UInt32(
                OldMachineTerm::ClickFunctionApplication {
                    name: "field_input".into(),
                    arguments: vec![arg],
                },
            ))
        };
        let values = vec![
            call(PureFunctionArgument::Value(ProgramValue::UInt32(
                word.clone(),
            ))),
            call(PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
            )),
            AlgebraicValue::Program(ProgramValue::Bool(OldMachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 2,
            })),
            AlgebraicValue::Program(ProgramValue::Float32(OldMachineTerm::uint32_constant(
                0x7fc00123,
            ))),
            AlgebraicValue::Program(ProgramValue::Float64(OldMachineTerm::uint64_constant(
                0x8000000000000000,
            ))),
            AlgebraicValue::Integer(IntegerTerm::Variable(Variable(10993303))),
            AlgebraicValue::Program(ProgramValue::typed_pointer(
                OldAddress::symbolic(Variable(10993304)),
                ProgramType::Int32Pointer,
            )),
        ];
        for a in &values {
            let native: NativeResourceArguments = vec![a.clone()].into();
            let fields = ResourceFieldValues::from(native.clone());
            let written = ResourceFieldValues::from_stored([StoredResourceField::Input(a.clone())]);
            assert_eq!(fields, written);
            assert_eq!(hash(&fields), hash(&written));
            assert_eq!(format!("{fields:?}"), format!("{native:?}"));
            assert_eq!(fields.get(0).unwrap().into_native(), *a);
            for b in &values {
                let other: NativeResourceArguments = vec![b.clone()].into();
                let stored = ResourceFieldValues::from(other.clone());
                assert_eq!(fields == stored, native == other);
                assert_eq!(fields.cmp(&stored), native.cmp(&other));
            }
        }
        let value = AlgebraicValue::Program(ProgramValue::UInt32(OldMachineTerm::Variable(
            Variable(10993305),
        )));
        let fields = ResourceFieldValues::from(vec![value.clone()]);
        let minted = ResourceFieldValues::from_minted(vec![value]);
        assert_eq!(fields, minted);
        assert_eq!(hash(&fields), hash(&minted));
    }

    #[test]
    fn field_projection_retains_the_existing_program_producer() {
        let _session = VerificationSession::enter();
        let fields = ResourceFieldValues::from_minted(vec![AlgebraicValue::Program(
            ProgramValue::UInt32(OldMachineTerm::Variable(Variable(10993306))),
        )]);
        let root = fields.program_value(0).unwrap().shared().unwrap().clone();
        let value = instance(fields, ProgramType::UInt32);
        assert!(
            !root.has_cached_native_argument(),
            "schema checking should read the root type"
        );
        assert!(value.fields.shares_storage_with(&value.clone().fields));
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(value))),
        );
        let expression = SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: InstanceId::from_variable(Variable(10993301)).into(),
                children: vec![],
                field_name: None,
                field_index: 0,
                at_entry: false,
            },
            program_type: ProgramType::UInt32,
        };
        let result = crate::kernel::program_evaluate_retained_spec_expression(
            &state,
            &expression,
            None,
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(result.value, root);
    }

    #[test]
    fn substitution_keeps_program_field_roots_for_changed_and_unchanged_values() {
        for ty in [
            ProgramType::Int8,
            ProgramType::UInt8,
            ProgramType::Int16,
            ProgramType::UInt16,
            ProgramType::Int32,
            ProgramType::UInt32,
        ] {
            let _session = VerificationSession::enter();
            let wrap = |bits| match ty {
                ProgramType::Int8 => crate::kernel::int8(bits),
                ProgramType::UInt8 => crate::kernel::uint8(bits),
                ProgramType::Int16 => crate::kernel::int16(bits),
                ProgramType::UInt16 => crate::kernel::uint16(bits),
                ProgramType::Int32 => crate::kernel::int32(bits),
                ProgramType::UInt32 => crate::kernel::uint32(bits),
                _ => unreachable!(),
            };
            let variable = Variable(10993307);
            let fields = ResourceFieldValues::from_minted(vec![AlgebraicValue::Program(wrap(
                OldMachineTerm::Variable(variable),
            ))]);
            let root = fields.program_value(0).unwrap().shared().unwrap().clone();
            let proposition = Proposition::ResourceViewable {
                point: Default::default(),
                memory: SymbolicMemory::new(),
                resource: Box::new(Resource::Instance(instance(fields, ty))),
            };
            for (from, expected) in [
                (Variable(10993308), wrap(OldMachineTerm::Variable(variable))),
                (variable, wrap(OldMachineTerm::constant(7))),
            ] {
                let mapped = crate::kernel::substitute_int32_variable_in_proposition(
                    &proposition,
                    from,
                    OldMachineTerm::constant(7),
                );
                let Proposition::ResourceViewable { resource, .. } = mapped else {
                    unreachable!()
                };
                let Resource::Instance(value) = *resource else {
                    unreachable!()
                };
                let result = value.fields().program_value(0).unwrap();
                assert!(result.shared().is_some());
                assert_eq!(result.native().as_ref(), &expected, "{ty:?}");
                if from != variable {
                    assert_eq!(result.shared(), Some(&root));
                }
            }
        }
    }

    #[test]
    fn logical_field_storage_keeps_integer_children_retained() {
        for algebraic in [false, true] {
            let _session = VerificationSession::enter();
            let child: SharedIntegerTerm = IntegerTerm::Add(
                IntegerTerm::var(Variable(10993501)).into(),
                IntegerTerm::constant_i64(7).into(),
            )
            .into();
            let weak = child.downgrade();
            let expression = IntegerTerm::Multiply(child.clone(), child);
            let (value, ty) = if algebraic {
                let ty =
                    KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]).algebraic_type;
                (
                    AlgebraicValue::Algebraic(AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: "Arm".into(),
                            fields: vec![AlgebraicValue::Integer(expression)],
                        },
                    }),
                    ResourceFieldType::Algebraic(ty),
                )
            } else {
                (
                    AlgebraicValue::Integer(expression),
                    ResourceFieldType::Integer,
                )
            };
            let fields = ResourceFieldValues::from_minted(vec![value]);
            let schema = ResourceFieldSchema::new(vec![("value".into(), ty)]).unwrap();
            assert!(fields.matches_schema(&schema));
            assert!(
                weak.upgrade()
                    .is_some_and(|root| !root.has_cached_native_argument()),
                "algebraic={algebraic}"
            );
        }
    }

    #[test]
    fn native_logical_field_inputs_keep_their_admission_and_identity() {
        let _session = VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Integer]).algebraic_type;
        let invalid = AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Missing".into(),
                fields: vec![],
            },
        });
        let schema = ResourceFieldSchema::new(vec![(
            "value".into(),
            ResourceFieldType::Algebraic(ty.clone()),
        )])
        .unwrap();
        let fields = ResourceFieldValues::from(vec![invalid]);
        assert!(!fields.matches_schema(&schema));
        let values = vec![
            AlgebraicValue::Integer(IntegerTerm::Add(
                IntegerTerm::var(Variable(10993502)).into(),
                IntegerTerm::constant_i64(7).into(),
            )),
            AlgebraicValue::Algebraic(AlgebraicTerm {
                algebraic_type: ty,
                node: AlgebraicTermNode::Variable(Variable(10993503)),
            }),
        ];
        let native: NativeResourceArguments = values.clone().into();
        let retained = ResourceFieldValues::from_minted(values);
        let written = ResourceFieldValues::from(native.clone());
        assert_eq!(retained, written);
        assert_eq!(hash(&retained), hash(&written));
        assert_eq!(format!("{retained:?}"), format!("{native:?}"));
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/resource_fields.rs");
    }
}
