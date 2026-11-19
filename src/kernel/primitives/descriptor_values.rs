//! Evaluated machine operands in immutable resource descriptors.
//! Native input and selected native output retain their exact syntax; shared
//! producers own their common root and reuse its existing compatibility reader.
use super::*;
use crate::kernel::{ExecutionValue, RetainedProgramValue};

#[derive(Clone)]
pub struct StoredMachineTerm(RetainedProgramValue);
impl From<MachineTerm> for StoredMachineTerm {
    fn from(value: MachineTerm) -> Self {
        Self::new(MachineIntegerType::Int32, value)
    }
}
impl From<u32> for StoredMachineTerm {
    fn from(value: u32) -> Self {
        MachineTerm::constant(value).into()
    }
}
impl StoredMachineTerm {
    pub(crate) fn new(ty: MachineIntegerType, value: MachineTerm) -> Self {
        let value = match ty {
            MachineIntegerType::Int8 => ProgramValue::Int8(value),
            MachineIntegerType::UInt8 => ProgramValue::UInt8(value),
            MachineIntegerType::Int16 => ProgramValue::Int16(value),
            MachineIntegerType::UInt16 => ProgramValue::UInt16(value),
            MachineIntegerType::Int32 => ProgramValue::Int32(value),
            MachineIntegerType::UInt32 => ProgramValue::UInt32(value),
            MachineIntegerType::Int64 => ProgramValue::Int64(value),
            MachineIntegerType::UInt64 => ProgramValue::UInt64(value),
            MachineIntegerType::Int128 => ProgramValue::Int128(value),
            MachineIntegerType::UInt128 => ProgramValue::UInt128(value),
        };
        Self(value.into())
    }
    /// Admission for the nominal 32-bit Term payload. Native inputs retain
    /// their written syntax; this does not widen or retag other root sorts.
    #[cfg(test)]
    pub(crate) fn from_word32_root(root: KernelTerm) -> Option<Self> {
        matches!(
            root.ty(),
            KernelType::Program(ProgramType::Int32 | ProgramType::UInt32)
        )
        .then(|| Self(ExecutionValue::Shared(root).into()))
    }
    pub(crate) fn from_value(value: ExecutionValue) -> Option<Self> {
        MachineIntegerType::from_program_type(value.program_type())?;
        if let ExecutionValue::Native(value) = &value
            && !matches!(
                value,
                ProgramValue::Int8(_)
                    | ProgramValue::UInt8(_)
                    | ProgramValue::Int16(_)
                    | ProgramValue::UInt16(_)
                    | ProgramValue::Int32(_)
                    | ProgramValue::UInt32(_)
                    | ProgramValue::Int64(_)
                    | ProgramValue::UInt64(_)
                    | ProgramValue::Int128(_)
                    | ProgramValue::UInt128(_)
            )
        {
            return None;
        }
        Some(Self(value.into()))
    }
    pub(crate) fn as_const(&self) -> Option<u32> {
        self.native_compat().as_const()
    }
    pub(crate) fn map_native(&self, rewrite: impl FnOnce(&MachineTerm) -> MachineTerm) -> Self {
        Self::new(
            MachineIntegerType::from_program_type(self.0.program_type())
                .expect("machine descriptor"),
            rewrite(self.native_compat()),
        )
    }
    pub(crate) fn operand_view(&self) -> MachineOperandView<'_> {
        match self.root() {
            Some(root) => MachineOperandView::Shared(root),
            None => MachineOperandView::Legacy(self.native_compat()),
        }
    }
    pub(crate) fn value(&self) -> &ExecutionValue {
        self.0.value()
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        self.0.root()
    }
    #[cfg(test)]
    pub(crate) fn into_native_compat(self) -> MachineTerm {
        match self.0.into_native_compat() {
            ProgramValue::Bool(value)
            | ProgramValue::Int8(value)
            | ProgramValue::UInt8(value)
            | ProgramValue::Int16(value)
            | ProgramValue::UInt16(value)
            | ProgramValue::Int32(value)
            | ProgramValue::UInt32(value)
            | ProgramValue::Int64(value)
            | ProgramValue::UInt64(value)
            | ProgramValue::Int128(value)
            | ProgramValue::UInt128(value) => value,
            _ => unreachable!("machine descriptor operand"),
        }
    }
    pub(crate) fn native_compat(&self) -> &MachineTerm {
        match self.0.native_compat() {
            ProgramValue::Bool(v)
            | ProgramValue::Int8(v)
            | ProgramValue::UInt8(v)
            | ProgramValue::Int16(v)
            | ProgramValue::UInt16(v)
            | ProgramValue::Int32(v)
            | ProgramValue::UInt32(v)
            | ProgramValue::Int64(v)
            | ProgramValue::UInt64(v)
            | ProgramValue::Int128(v)
            | ProgramValue::UInt128(v) => v,
            _ => unreachable!("machine descriptor operand"),
        }
    }
}
impl std::fmt::Debug for StoredMachineTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.native_compat().fmt(f)
    }
}
impl PartialEq for StoredMachineTerm {
    fn eq(&self, other: &Self) -> bool {
        matches!((self.root(), other.root()), (Some(a), Some(b)) if a == b)
            || self.native_compat() == other.native_compat()
    }
}
impl Eq for StoredMachineTerm {}
impl PartialOrd for StoredMachineTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for StoredMachineTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if matches!((self.root(), other.root()), (Some(a), Some(b)) if a == b) {
            std::cmp::Ordering::Equal
        } else {
            self.native_compat().cmp(other.native_compat())
        }
    }
}
impl std::hash::Hash for StoredMachineTerm {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.native_compat().hash(h);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    #[test]
    fn native_descriptor_machine_inputs_keep_exact_syntax_and_hash() {
        let _session = crate::kernel::VerificationSession::enter();
        fn hash(v: &impl Hash) -> u64 {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        }
        let values = [
            MachineTerm::constant(7),
            MachineTerm::uint32_constant(7),
            MachineTerm::uint64_constant(7),
            MachineTerm::Variable(Variable(10993613)),
        ];
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            for value in &values {
                let stored = StoredMachineTerm::new(ty, value.clone());
                assert_eq!(stored.native_compat(), value);
                assert_eq!(hash(&stored), hash(value));
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                for other in &values {
                    let other_stored = StoredMachineTerm::new(ty, other.clone());
                    assert_eq!(stored == other_stored, value == other);
                    assert_eq!(stored.cmp(&other_stored), value.cmp(other));
                }
            }
        }
    }
}

/// Exact program payload storage for protocol values and native output DTOs.
#[derive(Clone)]
pub struct StoredProgramValue(RetainedProgramValue);
impl From<ProgramValue> for StoredProgramValue {
    fn from(value: ProgramValue) -> Self {
        Self(value.into())
    }
}
impl From<ExecutionValue> for StoredProgramValue {
    fn from(value: ExecutionValue) -> Self {
        Self(
            crate::kernel::StoredExecutionValue::from(value)
                .into_value()
                .into(),
        )
    }
}
impl From<StoredProgramValue> for ProgramValue {
    fn from(value: StoredProgramValue) -> Self {
        value.0.into_native_compat()
    }
}
impl StoredProgramValue {
    pub(crate) fn value(&self) -> &ExecutionValue {
        self.0.value()
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        self.0.root()
    }
    pub(crate) fn native_compat(&self) -> &ProgramValue {
        self.0.native_compat()
    }
}

/// An exact native Integer field, or an already-produced common Integer.
#[derive(Clone)]
pub struct StoredIntegerTerm(StoredInteger);
#[derive(Clone)]
enum StoredInteger {
    Input(Arc<IntegerTerm>),
    Shared(KernelTerm),
}
impl From<IntegerTerm> for StoredIntegerTerm {
    fn from(value: IntegerTerm) -> Self {
        Self(StoredInteger::Input(Arc::new(value)))
    }
}
impl StoredIntegerTerm {
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        (root.ty() == &KernelType::Integer).then(|| Self(StoredInteger::Shared(root)))
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredInteger::Input(_) => None,
            StoredInteger::Shared(root) => Some(root),
        }
    }
    pub(crate) fn native_compat(&self) -> &IntegerTerm {
        match &self.0 {
            StoredInteger::Input(value) => value,
            StoredInteger::Shared(root) => {
                root.integer_native_compat().expect("Integer field output")
            }
        }
    }
    pub(crate) fn into_native_compat(self) -> IntegerTerm {
        match self.0 {
            StoredInteger::Input(value) => {
                Arc::try_unwrap(value).unwrap_or_else(|value| (*value).clone())
            }
            StoredInteger::Shared(root) => root
                .integer_native_compat()
                .expect("Integer field output")
                .clone(),
        }
    }
}

/// Exact algebraic field input and retained algebraic expression output.
#[derive(Clone)]
pub struct StoredAlgebraicTerm(StoredAlgebraic);
#[derive(Clone)]
enum StoredAlgebraic {
    Input(Arc<AlgebraicTerm>),
    Shared(KernelTerm),
}
impl From<AlgebraicTerm> for StoredAlgebraicTerm {
    fn from(value: AlgebraicTerm) -> Self {
        Self(StoredAlgebraic::Input(Arc::new(value)))
    }
}
impl StoredAlgebraicTerm {
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        matches!(root.ty(), KernelType::Algebraic(_)).then(|| Self(StoredAlgebraic::Shared(root)))
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredAlgebraic::Input(_) => None,
            StoredAlgebraic::Shared(root) => Some(root),
        }
    }
    pub(crate) fn into_native_compat(self) -> AlgebraicTerm {
        match self.0 {
            StoredAlgebraic::Input(value) => Arc::unwrap_or_clone(value),
            StoredAlgebraic::Shared(root) => KernelTermExport::default()
                .algebraic(&root)
                .expect("algebraic field output"),
        }
    }
    pub(crate) fn native_compat(&self) -> &AlgebraicTerm {
        match &self.0 {
            StoredAlgebraic::Input(value) => value,
            StoredAlgebraic::Shared(root) => root
                .algebraic_native_term()
                .expect("algebraic field output"),
        }
    }
}

/// A native condition input or one retained logical Bool root. Native output
/// reuses the root's existing Boolean argument slot rather than another cache.
#[derive(Clone)]
pub struct StoredConditionTerm(StoredCondition);
#[derive(Clone)]
enum StoredCondition {
    Input(Arc<ConditionTerm>),
    Shared(KernelTerm),
}
impl From<ConditionTerm> for StoredConditionTerm {
    fn from(value: ConditionTerm) -> Self {
        Self(StoredCondition::Input(Arc::new(value)))
    }
}
impl StoredConditionTerm {
    pub(crate) fn operand_view(&self) -> BooleanOperandView<'_> {
        match self.root() {
            Some(root) => BooleanOperandView::Shared(root),
            None => BooleanOperandView::Native(self.native_compat()),
        }
    }
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        (root.ty() == &KernelType::Bool).then(|| Self(StoredCondition::Shared(root)))
    }
    /// Already-evaluated scalar conditions produced by the loop guard checker.
    pub(crate) fn from_minted(value: ConditionTerm) -> Self {
        let root = KernelTermImport::for_exact_field_inputs().condition(&value);
        root.retain_native_condition_output(value);
        Self::from_root(root).expect("logical condition")
    }
    pub(crate) fn root(&self) -> Option<&KernelTerm> {
        match &self.0 {
            StoredCondition::Input(_) => None,
            StoredCondition::Shared(root) => Some(root),
        }
    }
    pub(crate) fn native_compat(&self) -> &ConditionTerm {
        match &self.0 {
            StoredCondition::Input(value) => value,
            StoredCondition::Shared(root) => {
                if let KernelTermNode::BoolLiteral(value) = root.node() {
                    return if *value {
                        &ConditionTerm::Constant(true)
                    } else {
                        &ConditionTerm::Constant(false)
                    };
                }
                let ProgramValue::Bool(MachineTerm::BoolCast { value, .. }) =
                    root.boolean_native().expect("logical Bool output")
                else {
                    unreachable!("condition output");
                };
                value
            }
        }
    }
}

macro_rules! native_descriptor_identity {
    ($carrier:ty) => {
        impl std::fmt::Debug for $carrier {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { self.native_compat().fmt(f) }
        }
        impl PartialEq for $carrier {
            fn eq(&self, other: &Self) -> bool {
                matches!((self.root(), other.root()), (Some(a), Some(b)) if a == b) || self.native_compat() == other.native_compat()
            }
        }
        impl Eq for $carrier {}
        impl PartialOrd for $carrier {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(other)) }
        }
        impl Ord for $carrier {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                if matches!((self.root(), other.root()), (Some(a), Some(b)) if a == b) { std::cmp::Ordering::Equal }
                else { self.native_compat().cmp(other.native_compat()) }
            }
        }
        impl std::hash::Hash for $carrier {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) { self.native_compat().hash(state); }
        }
    };
}
native_descriptor_identity!(StoredProgramValue);
native_descriptor_identity!(StoredIntegerTerm);
native_descriptor_identity!(StoredAlgebraicTerm);
native_descriptor_identity!(StoredConditionTerm);

#[cfg(test)]
mod protocol_value_tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    fn hash(value: &impl Hash) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut h);
        h.finish()
    }
    #[test]
    fn protocol_native_values_keep_exact_identity_and_scalar_conditions_round_trip() {
        let _session = crate::kernel::VerificationSession::enter();
        let values = [
            ProgramValue::Int32(MachineTerm::constant(7)),
            ProgramValue::UInt32(MachineTerm::uint32_constant(7)),
            ProgramValue::Bool(MachineTerm::constant(2)),
            ProgramValue::Float32(MachineTerm::uint32_constant(0x7fc00123)),
            ProgramValue::Float64(MachineTerm::uint64_constant(0x8000000000000000)),
        ];
        for value in &values {
            let stored = StoredProgramValue::from(value.clone());
            assert_eq!(hash(&stored), hash(value));
            assert_eq!(format!("{stored:?}"), format!("{value:?}"));
            for other in &values {
                let other_stored = StoredProgramValue::from(other.clone());
                assert_eq!(stored == other_stored, value == other);
                assert_eq!(stored.cmp(&other_stored), value.cmp(other));
            }
        }
        let conditions = [
            ConditionTerm::Constant(false),
            ConditionTerm::Constant(true),
            ConditionTerm::Variable(Variable(10993642)),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(10993643))),
                right: Box::new(MachineTerm::constant(1)),
            },
            ConditionTerm::BoolEqual(
                Box::new(ConditionTerm::Compare {
                    format: MachineIntegerType::UInt32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(MachineTerm::Variable(Variable(10993644))),
                    right: Box::new(MachineTerm::uint32_constant(1)),
                }),
                Box::new(ConditionTerm::Constant(false)),
            ),
        ];
        for value in &conditions {
            for stored in [
                StoredConditionTerm::from(value.clone()),
                StoredConditionTerm::from_minted(value.clone()),
            ] {
                assert_eq!(stored.native_compat(), value);
                assert_eq!(hash(&stored), hash(value));
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                for other in &conditions {
                    let other_stored = StoredConditionTerm::from(other.clone());
                    assert_eq!(stored == other_stored, value == other);
                    assert_eq!(stored.cmp(&other_stored), value.cmp(other));
                }
            }
        }
    }
    #[test]
    fn minted_condition_native_views_reuse_the_produced_output_without_exports() {
        let _session = crate::kernel::VerificationSession::enter();
        let value = MachineTerm::if_then_else(
            ConditionTerm::Variable(Variable(10993740)),
            MachineTerm::Variable(Variable(10993741)),
            MachineTerm::constant(3),
        );
        let native = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(value),
            right: Box::new(MachineTerm::constant(9)),
        };
        let exports = KernelTermExport::machine_export_count();
        let stored = StoredConditionTerm::from_minted(native.clone());
        assert!(stored.root().is_some());
        assert_eq!(stored.native_compat(), &native);
        assert_eq!(format!("{stored:?}"), format!("{native:?}"));
        let view = BooleanOperandView::Shared(stored.root().unwrap()).native();
        assert!(matches!(&view, std::borrow::Cow::Borrowed(_)));
        assert_eq!(view.as_ref(), &native);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn condition_proposition_storage_keeps_roots_and_native_fact_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        for condition in [
            ConditionTerm::Constant(false),
            ConditionTerm::Constant(true),
            ConditionTerm::Variable(Variable(10993711)),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(MachineTerm::Variable(Variable(10993712))),
                right: Box::new(MachineTerm::constant(9)),
            },
        ] {
            let root = KernelTermImport::for_exact_field_inputs().condition(&condition);
            for truth in [false, true] {
                let native = Proposition::condition_is(condition.clone(), truth);
                let shared = Proposition::condition_is(
                    StoredConditionTerm::from_root(root.clone()).unwrap(),
                    truth,
                );
                let Proposition::ConditionIs(stored, actual_truth) = shared.clone() else {
                    unreachable!();
                };
                assert_eq!(stored.root(), Some(&root));
                assert_eq!(actual_truth, truth);
                assert_eq!(shared, native);
                assert_eq!(shared.cmp(&native), std::cmp::Ordering::Equal);
                assert_eq!(hash(&shared), hash(&native));
                assert_eq!(format!("{shared:?}"), format!("{native:?}"));
                assert_eq!(shared.condition_native(), native.condition_native());
            }
        }
    }

    #[test]
    fn condition_proposition_visitors_keep_shared_substitution_and_native_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(10993713);
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(MachineTerm::constant(3)),
        };
        let root = KernelTermImport::for_exact_field_inputs().condition(&condition);
        let native = Proposition::condition_is(condition, false);
        let shared =
            Proposition::condition_is(StoredConditionTerm::from_root(root).unwrap(), false);
        for capture in [false, true] {
            let mut expected = Default::default();
            let mut actual = Default::default();
            if capture {
                crate::kernel::reasoning::collect_proposition_capture_variables(
                    &native,
                    &mut expected,
                );
                crate::kernel::reasoning::collect_proposition_capture_variables(
                    &shared,
                    &mut actual,
                );
            } else {
                crate::kernel::reasoning::collect_proposition_bitvector_variables(
                    &native,
                    &mut expected,
                );
                crate::kernel::reasoning::collect_proposition_bitvector_variables(
                    &shared,
                    &mut actual,
                );
            }
            assert_eq!(actual, expected);
            assert!(actual.contains(&variable));
        }
        let replacement = MachineTerm::Variable(Variable(10993714));
        let expected = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &native,
            variable,
            &replacement,
        );
        let actual = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &shared,
            variable,
            &replacement,
        );
        let Proposition::ConditionIs(stored, _) = &actual else {
            unreachable!();
        };
        assert!(stored.root().is_some());
        assert_eq!(actual, expected);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/descriptor_values.rs");
    }
}

// Selected native DTO view for existing output assertions. Production stores
// and value visitors retain their common operands.
#[cfg(test)]
impl ExpressionOutcome<StoredProgramValue> {
    pub(crate) fn native_compat(&self) -> ExpressionOutcome {
        self.clone().map_value(Into::into)
    }
}

#[cfg(test)]
mod proposition_outcome_tests {
    use super::*;
    #[test]
    fn expression_theorem_output_keeps_the_evaluators_common_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(10993661));
        let state = ExecutionState::new().with_retained_local("result", root.clone().into());
        let exports = KernelTermExport::machine_export_count();
        let theorem = crate::kernel::prove_program_expression_evaluation(
            state,
            ProgramExpression::Variable("result".into()),
        )
        .unwrap();
        let Proposition::ProgramExpressionEvaluates {
            outcome: ExpressionOutcome::Value(value),
            ..
        } = theorem.proposition()
        else {
            panic!("value");
        };
        assert_eq!(value.root(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn memory_load_theorem_output_keeps_the_cells_common_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = KernelTerm::variable(
            KernelType::Program(ProgramType::Float32),
            Variable(10993662),
        );
        let pointer = Address::symbolic(Variable(10993663));
        let memory = SymbolicMemory::new().store_retained(pointer.clone(), root.clone().into());
        let exports = KernelTermExport::machine_export_count();
        let theorem = crate::kernel::prove_memory_load(memory, pointer);
        let Proposition::MemoryLoads {
            outcome: ExpressionOutcome::Value(value),
            ..
        } = theorem.proposition()
        else {
            panic!("value");
        };
        assert_eq!(value.root(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[cfg(test)]
mod loadable_count_tests {
    use super::*;
    use std::hash::{Hash, Hasher};
    #[test]
    fn loadable_count_inputs_keep_exact_native_format_and_hash() {
        let _session = crate::kernel::VerificationSession::enter();
        let debug = |value: &dyn std::fmt::Debug| format!("{value:?}");
        for wide in [false, true] {
            for bytes in [
                MachineTerm::constant(7),
                MachineTerm::uint32_constant(7),
                MachineTerm::uint64_constant(7),
                MachineTerm::Variable(Variable(10993681)),
            ] {
                let stored = StoredMachineTerm::new(
                    if wide {
                        MachineIntegerType::UInt64
                    } else {
                        MachineIntegerType::Int32
                    },
                    bytes.clone(),
                );
                let fact = Proposition::MemoryLoadable {
                    memory: SymbolicMemory::new(),
                    base: Address::symbolic(Variable(10993682)),
                    bytes: stored,
                    wide,
                };
                let Proposition::MemoryLoadable {
                    bytes: stored,
                    wide: actual,
                    ..
                } = &fact
                else {
                    unreachable!()
                };
                assert_eq!(*actual, wide);
                assert_eq!(stored.native_compat(), &bytes);
                assert_eq!(debug(stored), debug(&bytes));
                let mut a = std::collections::hash_map::DefaultHasher::new();
                let mut b = std::collections::hash_map::DefaultHasher::new();
                stored.hash(&mut a);
                bytes.hash(&mut b);
                assert_eq!(a.finish(), b.finish());
            }
        }
    }
}

#[cfg(test)]
mod term_payload_contract_tests {
    use super::*;
    use crate::kernel::VerificationSession;
    use std::hash::{Hash, Hasher};

    fn hash(value: &impl Hash) -> u64 {
        let mut state = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut state);
        state.finish()
    }

    fn algebraic(pointer: Pointer) -> AlgebraicTerm {
        let mut value = KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(
            ProgramType::Int32Pointer,
        )]);
        value.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(pointer))],
        };
        value
    }

    #[test]
    fn integer_and_algebraic_carriers_preserve_exact_native_identity() {
        let _session = VerificationSession::enter();
        let integers = [
            IntegerTerm::constant_i64(7),
            IntegerTerm::Variable(Variable(991700)),
            IntegerTerm::Add(
                IntegerTerm::Variable(Variable(991700)).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
        ];
        for value in &integers {
            let stored = StoredIntegerTerm::from(value.clone());
            assert!(stored.root().is_none());
            assert_eq!(stored.native_compat(), value);
            assert_eq!(hash(&stored), hash(value));
            assert_eq!(format!("{stored:?}"), format!("{value:?}"));
            for other in &integers {
                let other_stored = StoredIntegerTerm::from(other.clone());
                assert_eq!(stored == other_stored, value == other);
                assert_eq!(stored.cmp(&other_stored), value.cmp(other));
            }
            let retained = StoredIntegerTerm::from_root(
                KernelTermImport::for_exact_field_inputs().integer(&value.clone().into()),
            )
            .unwrap();
            assert_eq!(retained.native_compat(), value);
            assert_eq!(retained, stored);
            assert_eq!(hash(&retained), hash(value));
            assert_eq!(stored.into_native_compat(), *value);
        }
        let pointer = Pointer::new(
            Address::symbolic(Variable(991701)),
            ProgramType::Int32Pointer,
        );
        let values = [
            algebraic(pointer.clone()),
            algebraic(pointer.with_pointee_constant(true)),
        ];
        for value in &values {
            let input = StoredAlgebraicTerm::from(value.clone());
            let root = KernelTermImport::for_exact_field_inputs().algebraic(value);
            let retained = StoredAlgebraicTerm::from_root(root).unwrap();
            assert!(input.root().is_none());
            for stored in [&input, &retained] {
                assert_eq!(stored.native_compat(), value);
                assert_eq!(format!("{stored:?}"), format!("{value:?}"));
                assert_eq!(hash(stored), hash(value));
                for other in &values {
                    let other = StoredAlgebraicTerm::from(other.clone());
                    assert_eq!(stored == &other, value == other.native_compat());
                    assert_eq!(stored.cmp(&other), value.cmp(other.native_compat()));
                }
            }
            let pointer = |value: &AlgebraicTerm| {
                let AlgebraicTermNode::Constructor { fields, .. } = &value.node else {
                    unreachable!()
                };
                let AlgebraicValue::Program(ProgramValue::Pointer(pointer)) = &fields[0] else {
                    unreachable!()
                };
                pointer.pointee_constant()
            };
            assert_eq!(pointer(retained.native_compat()), pointer(value));
        }
    }

    #[test]
    fn word32_root_admission_preserves_native_format_and_rejects_other_sorts() {
        let _session = VerificationSession::enter();
        for format in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
            let variables = [Variable(991710), Variable(991711)];
            let root = KernelTerm::arithmetic_binary(
                format,
                MachineBinaryOp::Add,
                variables.map(|variable| {
                    KernelTerm::variable(KernelType::Program(format.program_type()), variable)
                }),
            )
            .unwrap();
            let stored = StoredMachineTerm::from_word32_root(root.clone()).unwrap();
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(stored.clone().root().map(KernelTerm::id), Some(root.id()));
            assert!(!root.has_cached_native_argument());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let native = MachineTerm::Binary {
                format,
                op: MachineBinaryOp::Add,
                left: Box::new(MachineTerm::Variable(variables[0])),
                right: Box::new(MachineTerm::Variable(variables[1])),
            };
            let input = StoredMachineTerm::from(native.clone());
            assert_eq!(stored.native_compat(), &native);
            assert_eq!(stored, input);
            assert_eq!(hash(&stored), hash(&native));
            assert_eq!(stored.into_native_compat(), native);
        }
        for ty in [
            KernelType::Integer,
            KernelType::Bool,
            KernelType::Program(ProgramType::UInt64),
            KernelType::Program(ProgramType::Int16),
            KernelType::Program(ProgramType::Float32),
        ] {
            let root = KernelTerm::variable(ty, Variable(991712));
            assert!(StoredMachineTerm::from_word32_root(root.clone()).is_none());
            assert!(!root.has_cached_native_argument());
        }
    }

    #[test]
    fn retained_and_native_payload_clones_keep_growing_prefixes_unmaterialized() {
        let _session = VerificationSession::enter();
        let ty = KernelMatch::test_scrutinee(Vec::new()).algebraic_type;
        for size in [16, 64, 256] {
            let mut integer = KernelTerm::variable(KernelType::Integer, Variable(991720));
            let mut algebraic =
                KernelTerm::variable(KernelType::Algebraic(ty.clone()), Variable(991721));
            for _ in 0..size {
                integer = KernelTerm::integer_operation(
                    KernelIntegerOperator::Add,
                    vec![integer.clone(), integer],
                )
                .unwrap();
                algebraic = KernelTerm::algebraic_call(
                    ty.clone(),
                    "stored_shared_dag".into(),
                    vec![(algebraic.clone(), None), (algebraic, None)],
                );
            }
            let exports = (
                KernelTermExport::machine_export_count(),
                KernelTermExport::algebraic_export_count(),
            );
            let integers = StoredIntegerTerm::from_root(integer.clone()).unwrap();
            let algebraics = StoredAlgebraicTerm::from_root(algebraic.clone()).unwrap();
            for _ in 0..32 {
                assert_eq!(
                    integers.clone().root().map(KernelTerm::id),
                    Some(integer.id())
                );
                assert_eq!(
                    algebraics.clone().root().map(KernelTerm::id),
                    Some(algebraic.id())
                );
                assert!(!integer.has_cached_native_argument());
                assert!(!algebraic.has_cached_native_argument());
            }
            assert_eq!(
                (
                    KernelTermExport::machine_export_count(),
                    KernelTermExport::algebraic_export_count()
                ),
                exports
            );
            let native = StoredIntegerTerm::from(IntegerTerm::Variable(Variable(991722)));
            assert!(std::ptr::eq(
                native.native_compat(),
                native.clone().native_compat()
            ));
        }
    }

    #[test]
    fn consuming_program_storage_moves_an_owned_native_address_prefix() {
        for size in [16, 64, 256] {
            let mut offset = AddressOffset::Constant(0);
            for index in 0..size {
                offset = AddressOffset::Add(
                    Box::new(offset),
                    Box::new(AddressOffset::Variable(Variable(991730 + index))),
                );
            }
            let value = ProgramValue::pointer(Address {
                base: AddressBase::Symbolic(Variable(991729)),
                offset,
            });
            let ProgramValue::Pointer(pointer) = &value else {
                unreachable!()
            };
            let AddressOffset::Add(left, right) = &pointer.address().offset else {
                unreachable!()
            };
            let allocations = [
                std::ptr::from_ref(left.as_ref()),
                std::ptr::from_ref(right.as_ref()),
            ];
            let value = ProgramValue::from(StoredProgramValue::from(value));
            let ProgramValue::Pointer(pointer) = value else {
                unreachable!()
            };
            let address = pointer.into_pointer();
            let AddressOffset::Add(left, right) = &address.offset else {
                unreachable!()
            };
            assert_eq!(
                [
                    std::ptr::from_ref(left.as_ref()),
                    std::ptr::from_ref(right.as_ref())
                ],
                allocations
            );
        }
    }
}
