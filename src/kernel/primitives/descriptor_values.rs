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
