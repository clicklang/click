//! Named program-value storage. Native lookups are selected compatibility
//! outputs; the map owns common roots and never exports an ambient environment.
use super::*;
use crate::kernel::{ExecutionValue, RetainedProgramValue};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct ProgramValueBindings(BTreeMap<String, RetainedProgramValue>);

impl ProgramValueBindings {
    pub(super) fn new() -> Self {
        Self::default()
    }
    pub(super) fn len(&self) -> usize {
        self.0.len()
    }
    pub(super) fn contains_key(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }
    pub(super) fn get(&self, name: &str) -> Option<&ProgramValue> {
        self.0.get(name).map(RetainedProgramValue::native_compat)
    }
    pub(super) fn get_retained(&self, name: &str) -> Option<&RetainedProgramValue> {
        self.0.get(name)
    }
    pub(super) fn insert(
        &mut self,
        name: String,
        value: ProgramValue,
    ) -> Option<RetainedProgramValue> {
        self.0.insert(name, value.into())
    }
    pub(super) fn insert_retained(
        &mut self,
        name: String,
        value: impl Into<RetainedProgramValue>,
    ) -> Option<RetainedProgramValue> {
        self.0.insert(name, value.into())
    }
    pub(super) fn keys(&self) -> impl DoubleEndedIterator<Item = &String> + ExactSizeIterator {
        self.0.keys()
    }
    pub(super) fn iter_retained(
        &self,
    ) -> impl DoubleEndedIterator<Item = (&String, &RetainedProgramValue)> + ExactSizeIterator {
        self.0.iter()
    }
    pub(super) fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = (&String, &ProgramValue)> + ExactSizeIterator {
        self.0
            .iter()
            .map(|(name, value)| (name, value.native_compat()))
    }
    pub(super) fn values(
        &self,
    ) -> impl DoubleEndedIterator<Item = &ProgramValue> + ExactSizeIterator {
        self.0.values().map(RetainedProgramValue::native_compat)
    }
}
impl FromIterator<(String, ProgramValue)> for ProgramValueBindings {
    fn from_iter<T: IntoIterator<Item = (String, ProgramValue)>>(values: T) -> Self {
        Self(
            values
                .into_iter()
                .map(|(name, value)| (name, value.into()))
                .collect(),
        )
    }
}
impl From<BTreeMap<String, ProgramValue>> for ProgramValueBindings {
    fn from(values: BTreeMap<String, ProgramValue>) -> Self {
        values.into_iter().collect()
    }
}
impl Extend<(String, ProgramValue)> for ProgramValueBindings {
    fn extend<T: IntoIterator<Item = (String, ProgramValue)>>(&mut self, values: T) {
        self.0
            .extend(values.into_iter().map(|(name, value)| (name, value.into())));
    }
}
impl IntoIterator for ProgramValueBindings {
    type Item = (String, ProgramValue);
    type IntoIter = std::iter::Map<
        std::collections::btree_map::IntoIter<String, RetainedProgramValue>,
        fn((String, RetainedProgramValue)) -> (String, ProgramValue),
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.0
            .into_iter()
            .map(|(name, value)| (name, value.into_native_compat()))
    }
}
impl<'a> IntoIterator for &'a ProgramValueBindings {
    type Item = (&'a String, &'a ProgramValue);
    type IntoIter = std::iter::Map<
        std::collections::btree_map::Iter<'a, String, RetainedProgramValue>,
        fn((&'a String, &'a RetainedProgramValue)) -> (&'a String, &'a ProgramValue),
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.0
            .iter()
            .map(|(name, value)| (name, value.native_compat()))
    }
}
impl std::ops::Index<&str> for ProgramValueBindings {
    type Output = ProgramValue;
    fn index(&self, name: &str) -> &Self::Output {
        self.get(name).expect("program binding")
    }
}
impl std::ops::Index<&String> for ProgramValueBindings {
    type Output = ProgramValue;
    fn index(&self, name: &String) -> &Self::Output {
        &self[name.as_str()]
    }
}

impl<const N: usize> From<[(String, ProgramValue); N]> for ProgramValueBindings {
    fn from(values: [(String, ProgramValue); N]) -> Self {
        values.into_iter().collect()
    }
}
impl crate::kernel::NamedBindingMap<ProgramValue> for ProgramValueBindings {
    fn get_named(&self, name: &str) -> Option<&ProgramValue> {
        self.get(name)
    }
}

impl FromIterator<(String, RetainedProgramValue)> for ProgramValueBindings {
    fn from_iter<T: IntoIterator<Item = (String, RetainedProgramValue)>>(values: T) -> Self {
        Self(values.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelType, MachineBinaryOp, MachineIntegerType, Variable};

    #[test]
    fn retained_bindings_select_one_native_output_and_keep_handoff_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996931));
        let other =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt64), Variable(996932));
        let mut values = ProgramValueBindings::new();
        values.insert_retained("chosen".into(), ExecutionValue::Shared(root.clone()));
        values.insert_retained("unrelated".into(), ExecutionValue::Shared(other.clone()));
        assert_eq!(values.get_retained("chosen").unwrap().root(), Some(&root));
        assert!(!root.has_cached_native_argument());
        assert!(!other.has_cached_native_argument());
        let copy = values.clone();
        assert_eq!(
            copy.get("chosen"),
            Some(&ProgramValue::UInt64(MachineTerm::Variable(Variable(
                996931
            ))))
        );
        assert!(!other.has_cached_native_argument());
        assert_eq!(
            copy.get_retained("chosen")
                .unwrap()
                .clone()
                .into_value()
                .shared(),
            Some(&root)
        );
    }

    #[test]
    fn retained_program_values_preserve_native_call_forms_bits_and_metadata() {
        use crate::kernel::{
            AlgebraicTerm, AlgebraicTermNode, PureFunctionArgument, TypeParameterName,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let values = [
            ProgramValue::Bool(MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 2,
            }),
            ProgramValue::Float32(MachineTerm::uint32_constant(0x7fc00123)),
            ProgramValue::Float64(MachineTerm::uint64_constant(0x8000000000000000)),
            ProgramValue::Int32(MachineTerm::ClickFunctionApplication {
                name: "retained_argument".into(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::UInt64(
                    MachineTerm::uint64_constant(9),
                ))],
            }),
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(996937)),
                ProgramType::Int32Pointer,
            )
            .with_pointer_pointee_constant(true)
            .with_pointer_pointee_volatile(true),
            ProgramValue::Parameter(Box::new(AlgebraicTerm {
                algebraic_type: TypeParameterName::intern("RetainedArgumentT").algebraic_type(),
                node: AlgebraicTermNode::Variable(Variable(996938)),
            })),
            ProgramValue::Void,
        ];
        for value in values {
            let stored = RetainedProgramValue::from(value.clone());
            assert_eq!(stored.native_compat(), &value);
            assert_eq!(
                format!("{:?}", stored.native_compat()),
                format!("{value:?}")
            );
            assert_eq!(stored.clone(), RetainedProgramValue::from(value));
        }
    }

    #[test]
    fn native_call_argument_carrier_identity_survives_storage() {
        use crate::kernel::{PureFunctionArgument, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let word = MachineTerm::Variable(Variable(996939));
        let call = |argument| {
            ProgramValue::UInt32(MachineTerm::ClickFunctionApplication {
                name: "retained_call_identity".into(),
                arguments: vec![argument],
            })
        };
        let a = call(PureFunctionArgument::Value(ProgramValue::UInt32(
            word.clone(),
        )));
        let b = call(PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
        ));
        assert_ne!(a, b);
        let stored_a = RetainedProgramValue::from(a.clone());
        let stored_b = RetainedProgramValue::from(b.clone());
        assert_ne!(stored_a, stored_b);
        assert_eq!(stored_a.native_compat(), &a);
        assert_eq!(stored_b.native_compat(), &b);
    }

    #[test]
    fn recorded_values_keep_native_naming_and_replace_loop_count_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut states = RecordedStates::new();
        let native = ProgramValue::UInt64(MachineTerm::Variable(Variable(996933)));
        states.record_call_result(7, Some(native.clone()));
        assert_eq!(states.call_result_native(&7), Some(&native));
        let old = crate::kernel::Variable(996934);
        let new = crate::kernel::Variable(996935);
        states.record_loop_iterations(4, &crate::kernel::IntegerTerm::Variable(old));
        let copy = states.clone();
        assert_eq!(copy.loop_naming_iterations(old), Some(4));
        states.record_loop_iterations(4, &crate::kernel::IntegerTerm::Variable(new));
        assert_eq!(states.loop_naming_iterations(old), None);
        assert_eq!(states.loop_naming_iterations(new), Some(4));
        assert_eq!(copy.loop_naming_iterations(old), Some(4));
    }

    mod scaling_tests {
        use super::*;
        include!("../scaling_tests/surface/program_values.rs");
    }
}
