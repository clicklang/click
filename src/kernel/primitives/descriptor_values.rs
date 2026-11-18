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
    pub(crate) fn from_value(value: ExecutionValue) -> Option<Self> {
        MachineIntegerType::from_program_type(value.program_type())?;
        if let ExecutionValue::Native(value) = &value {
            if !matches!(
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
            ) {
                return None;
            }
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
        value.native_compat().clone()
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
    pub(crate) fn from_root(root: KernelTerm) -> Option<Self> {
        (root.ty() == &KernelType::Bool).then(|| Self(StoredCondition::Shared(root)))
    }
    /// Already-evaluated scalar conditions produced by the loop guard checker.
    pub(crate) fn from_minted(value: ConditionTerm) -> Self {
        Self::from_root(KernelTermImport::for_exact_field_inputs().condition(&value))
            .expect("logical condition")
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
    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/descriptor_values.rs");
    }
}

// Both outcome schemas use exact native value identity, rather than execution
// observation equality. This comparison is the explicit native DTO boundary.
impl PartialEq<ExpressionOutcome<ProgramValue>> for ExpressionOutcome<StoredProgramValue> {
    fn eq(&self, other: &ExpressionOutcome<ProgramValue>) -> bool {
        match (self, other) {
            (Self::Value(a), ExpressionOutcome::Value(b)) => a.native_compat() == b,
            (Self::UndefinedBehavior(a), ExpressionOutcome::UndefinedBehavior(b)) => a == b,
            (Self::RuntimeError(a), ExpressionOutcome::RuntimeError(b)) => a == b,
            _ => false,
        }
    }
}
impl PartialEq<ExpressionOutcome<StoredProgramValue>> for ExpressionOutcome<ProgramValue> {
    fn eq(&self, other: &ExpressionOutcome<StoredProgramValue>) -> bool {
        other == self
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
