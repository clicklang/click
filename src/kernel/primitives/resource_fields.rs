//! Immutable resource fields. Program producers keep their execution carrier;
//! native input lists and selected compatibility readers stay explicit.
use super::*;
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
impl ResourceFieldValue<'_> {
    pub(crate) fn into_native(self) -> AlgebraicValue {
        match self {
            Self::Program(value) => AlgebraicValue::Program(value.clone()),
            Self::Integer(value) => AlgebraicValue::Integer(value.clone()),
            Self::Algebraic(value) => AlgebraicValue::Algebraic(value.clone()),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum StoredResourceField {
    Input(AlgebraicValue),
    Program(RetainedProgramValue),
}
impl StoredResourceField {
    pub(crate) fn from_minted(value: AlgebraicValue) -> Self {
        match value {
            AlgebraicValue::Program(value) => {
                let root =
                    KernelTermImport::default().argument(&PureFunctionArgument::Value(value));
                Self::from_program(ExecutionValue::Shared(root))
            }
            value => Self::Input(value),
        }
    }
    pub(crate) fn from_program(value: ExecutionValue) -> Self {
        match StoredExecutionValue::from(value).into_value() {
            ExecutionValue::Native(value) => Self::Input(AlgebraicValue::Program(value)),
            value => Self::Program(value.into()),
        }
    }
    fn native(&self) -> ResourceFieldValue<'_> {
        match self {
            Self::Input(value) => value.into(),
            Self::Program(value) => ResourceFieldValue::Program(value.native_compat()),
        }
    }
}

#[derive(Clone)]
pub struct ResourceFieldValues(Arc<FieldStorage>);
enum FieldStorage {
    Input(ResourceArguments),
    Retained(Box<[StoredResourceField]>),
}
impl ResourceFieldValues {
    pub fn len(&self) -> usize {
        match self.0.as_ref() {
            FieldStorage::Input(values) => values.len(),
            FieldStorage::Retained(values) => values.len(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn get(&self, index: usize) -> Option<ResourceFieldValue<'_>> {
        match self.0.as_ref() {
            FieldStorage::Input(values) => values.get(index).map(ResourceFieldValue::from),
            FieldStorage::Retained(values) => values.get(index).map(StoredResourceField::native),
        }
    }
    pub fn iter(&self) -> ResourceFieldIter<'_> {
        ResourceFieldIter {
            values: self,
            range: 0..self.len(),
        }
    }
    pub(crate) fn program_value(&self, index: usize) -> Option<ExecutionValue> {
        match self.0.as_ref() {
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
        match self.0.as_ref() {
            FieldStorage::Input(values) => {
                values.get(index).cloned().map(StoredResourceField::Input)
            }
            FieldStorage::Retained(values) => values.get(index).cloned(),
        }
    }
    pub(crate) fn from_stored(values: impl IntoIterator<Item = StoredResourceField>) -> Self {
        Self(Arc::new(FieldStorage::Retained(
            values.into_iter().collect(),
        )))
    }
    /// Fresh fields are typed symbolic leaves minted by the existing factory.
    /// Native public inputs use `From<ResourceArguments>` instead.
    pub(crate) fn from_minted(values: Vec<AlgebraicValue>) -> Self {
        Self::from_stored(values.into_iter().map(StoredResourceField::from_minted))
    }
    pub(crate) fn retained_program(&self, index: usize) -> Option<&ExecutionValue> {
        match self.0.as_ref() {
            FieldStorage::Retained(values) => match values.get(index)? {
                StoredResourceField::Program(value) => Some(value.value()),
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
        match self.0.as_ref() {
            FieldStorage::Input(values) => Cow::Borrowed(values),
            FieldStorage::Retained(_) => Cow::Owned(self.to_vec()),
        }
    }
    pub(crate) fn matches_schema(&self, schema: &ResourceFieldSchema) -> bool {
        if self.len() != schema.fields().len() {
            return false;
        }
        schema.fields().iter().enumerate().all(|(index, (_, ty))| {
            if let FieldStorage::Retained(values) = self.0.as_ref()
                && let StoredResourceField::Program(value) = &values[index]
            {
                return matches!(ty, ResourceFieldType::Program(expected) if *expected == value.program_type());
            }
            match (ty, self.get(index).expect("field index")) {
                (ResourceFieldType::Integer, ResourceFieldValue::Integer(_)) => true,
                (ResourceFieldType::Program(ty), ResourceFieldValue::Program(value)) => *ty == value.program_type(),
                (ResourceFieldType::Algebraic(ty), ResourceFieldValue::Algebraic(value)) => *ty == value.algebraic_type && value.is_well_formed(),
                _ => false,
            }
        })
    }
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl From<ResourceArguments> for ResourceFieldValues {
    fn from(values: ResourceArguments) -> Self {
        Self(Arc::new(FieldStorage::Input(values)))
    }
}
impl From<Vec<AlgebraicValue>> for ResourceFieldValues {
    fn from(values: Vec<AlgebraicValue>) -> Self {
        ResourceArguments::from(values).into()
    }
}
impl<const N: usize> From<[AlgebraicValue; N]> for ResourceFieldValues {
    fn from(values: [AlgebraicValue; N]) -> Self {
        Vec::from(values).into()
    }
}
impl FromIterator<AlgebraicValue> for ResourceFieldValues {
    fn from_iter<T: IntoIterator<Item = AlgebraicValue>>(values: T) -> Self {
        values.into_iter().collect::<ResourceArguments>().into()
    }
}
impl std::fmt::Debug for ResourceFieldValues {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl PartialEq for ResourceFieldValues {
    fn eq(&self, other: &Self) -> bool {
        self.shares_storage_with(other)
            || (self.len() == other.len() && self.iter().eq(other.iter()))
    }
}
impl Eq for ResourceFieldValues {}
impl Ord for ResourceFieldValues {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.iter().cmp(other.iter())
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
        for value in self.iter() {
            value.hash(state);
        }
    }
}
impl PartialEq<[AlgebraicValue]> for ResourceFieldValues {
    fn eq(&self, other: &[AlgebraicValue]) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter().map(ResourceFieldValue::from))
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
impl PartialEq<ResourceArguments> for ResourceFieldValues {
    fn eq(&self, other: &ResourceArguments) -> bool {
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
            Variable(10993301),
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
        let word = MachineTerm::Variable(Variable(10993302));
        let call = |arg| {
            AlgebraicValue::Program(ProgramValue::UInt32(
                MachineTerm::ClickFunctionApplication {
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
            AlgebraicValue::Program(ProgramValue::Bool(MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 2,
            })),
            AlgebraicValue::Program(ProgramValue::Float32(MachineTerm::uint32_constant(
                0x7fc00123,
            ))),
            AlgebraicValue::Program(ProgramValue::Float64(MachineTerm::uint64_constant(
                0x8000000000000000,
            ))),
            AlgebraicValue::Integer(IntegerTerm::Variable(Variable(10993303))),
            AlgebraicValue::Program(
                ProgramValue::typed_pointer(
                    Address::symbolic(Variable(10993304)),
                    ProgramType::Int32Pointer,
                )
                .with_pointer_pointee_constant(true),
            ),
        ];
        for a in &values {
            let native: ResourceArguments = vec![a.clone()].into();
            let fields = ResourceFieldValues::from(native.clone());
            assert_eq!(hash(&fields), hash(&native));
            assert_eq!(format!("{fields:?}"), format!("{native:?}"));
            assert_eq!(fields.get(0).unwrap().into_native(), *a);
            for b in &values {
                let other: ResourceArguments = vec![b.clone()].into();
                let stored = ResourceFieldValues::from(other.clone());
                assert_eq!(fields == stored, native == other);
                assert_eq!(fields.cmp(&stored), native.cmp(&other));
            }
        }
        let fields = ResourceFieldValues::from_minted(vec![AlgebraicValue::Program(
            ProgramValue::UInt32(MachineTerm::Variable(Variable(10993305))),
        )]);
        let native: ResourceArguments = fields.to_vec().into();
        assert_eq!(hash(&fields), hash(&native));
        assert_eq!(fields, ResourceFieldValues::from(native));
    }

    #[test]
    fn field_projection_retains_the_existing_program_producer() {
        let _session = VerificationSession::enter();
        let fields = ResourceFieldValues::from_minted(vec![AlgebraicValue::Program(
            ProgramValue::UInt32(MachineTerm::Variable(Variable(10993306))),
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
                identity: Variable(10993301),
                children: vec![],
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
        let _session = VerificationSession::enter();
        let variable = Variable(10993307);
        let fields = ResourceFieldValues::from_minted(vec![AlgebraicValue::Program(
            ProgramValue::Int32(MachineTerm::Variable(variable)),
        )]);
        let root = fields.program_value(0).unwrap().shared().unwrap().clone();
        let proposition = Proposition::ResourceViewable {
            memory: SymbolicMemory::new(),
            resource: Box::new(Resource::Instance(instance(fields, ProgramType::Int32))),
        };
        for (from, expected) in [
            (
                Variable(10993308),
                ProgramValue::Int32(MachineTerm::Variable(variable)),
            ),
            (variable, ProgramValue::Int32(MachineTerm::constant(7))),
        ] {
            let mapped = crate::kernel::substitute_int32_variable_in_proposition(
                &proposition,
                from,
                MachineTerm::constant(7),
            );
            let Proposition::ResourceViewable { resource, .. } = mapped else {
                unreachable!()
            };
            let Resource::Instance(value) = *resource else {
                unreachable!()
            };
            let result = value.fields().program_value(0).unwrap();
            assert!(result.shared().is_some());
            assert_eq!(result.native().as_ref(), &expected);
            if from != variable {
                assert_eq!(result.shared(), Some(&root));
            }
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/resource_fields.rs");
    }
}
