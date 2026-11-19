//! Typed observations produced by logical reads. Consumers use these values,
//! never reconstruct their address/provenance from caches or memory history.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(in crate::kernel) enum ReadType {
    Pointer(ProgramType),
    Abstract,
    IntegerAddress,
    Integer(MachineIntegerType),
}

impl ReadType {
    fn key(self) -> Self {
        // Equality of 64-bit words uses Int64 in the kernel, irrespective of
        // signedness. Preserve the producer's bits under that same identity.
        match self {
            Self::Integer(MachineIntegerType::UInt64) => Self::Integer(MachineIntegerType::Int64),
            other => other,
        }
    }

    pub(in crate::kernel) fn bytes(self) -> u32 {
        match self {
            Self::Pointer(_) | Self::IntegerAddress => C_POINTER_BYTE_WIDTH,
            Self::Abstract => ABSTRACT_VALUE_WIDTH,
            Self::Integer(format) => format.program_type().byte_width(),
        }
    }
}

use crate::kernel::program_point::ProgramPointId;

type ReadKey = (SharedMemory, Address, ReadType, Option<ProgramPointId>);
type Reads = imbl::HashMap<ReadKey, ProgramValue>;
thread_local! {
    static READS: std::cell::RefCell<Option<Reads>> = const { std::cell::RefCell::new(None) };
}

/// Retain observations only while lowering and applying an explicit preservation step.
/// Nested scopes have isolated tables; dropping a scope restores its caller.
pub(crate) struct ReadScope(Option<Reads>);
impl ReadScope {
    pub(crate) fn enter() -> Self {
        Self(READS.with(|reads| reads.replace(Some(Reads::new()))))
    }
}
impl Drop for ReadScope {
    fn drop(&mut self) {
        READS.with(|reads| *reads.borrow_mut() = self.0.take());
    }
}

pub(super) fn record(memory: &SymbolicMemory, address: &Address, value: &ProgramValue) {
    if !READS.with(|reads| reads.borrow().is_some()) {
        return;
    }
    let value = value.numeric_value();
    let kind = match value {
        ProgramValue::Pointer(p) => ReadType::Pointer(p.program_type()),
        ProgramValue::Parameter(_) => ReadType::Abstract,
        ProgramValue::Int16(_) => ReadType::Integer(MachineIntegerType::Int16),
        ProgramValue::UInt16(_) => ReadType::Integer(MachineIntegerType::UInt16),
        ProgramValue::Int32(_) => ReadType::Integer(MachineIntegerType::Int32),
        ProgramValue::UInt32(_) => ReadType::Integer(MachineIntegerType::UInt32),
        ProgramValue::Int8(_) => ReadType::Integer(MachineIntegerType::Int8),
        ProgramValue::UInt8(_) => ReadType::Integer(MachineIntegerType::UInt8),
        ProgramValue::Int64(_) => ReadType::Integer(MachineIntegerType::Int64),
        ProgramValue::UInt64(_) => ReadType::Integer(MachineIntegerType::UInt64),
        _ => return,
    };
    crate::instrumentation::record_deterministic_work(1);
    let kind = kind.key();
    let version = match value {
        ProgramValue::Int8(MachineTerm::MemoryLoad(point, _, LoadKind::Int8))
        | ProgramValue::UInt8(MachineTerm::MemoryLoad(point, _, LoadKind::UInt8))
        | ProgramValue::Int16(MachineTerm::MemoryLoad(point, _, LoadKind::Int16))
        | ProgramValue::UInt16(MachineTerm::MemoryLoad(point, _, LoadKind::UInt16))
        | ProgramValue::Int32(MachineTerm::MemoryLoad(point, _, LoadKind::Int32))
        | ProgramValue::UInt32(MachineTerm::MemoryLoad(point, _, LoadKind::UInt32)) => {
            point.read_version_id()
        }
        _ => None,
    };
    let memory = crate::kernel::intern_memory_ref(memory);
    READS.with(|reads| {
        let mut slot = reads.borrow_mut();
        let reads = slot.as_mut().expect("active typed read scope");
        reads.insert(
            (memory.clone(), address.clone(), kind, version),
            value.clone(),
        );
        if matches!(kind, ReadType::Pointer(_)) {
            reads.insert(
                (memory, address.clone(), ReadType::IntegerAddress, None),
                value.clone(),
            );
        }
    });
}

/// Only the producer can file observations. A missing entry is not permission
/// to evaluate a read here. The preservation goal names its reads by lowering
/// them before applying the primitive.
#[cfg(test)]
pub(in crate::kernel) fn get(
    memory: &SymbolicMemory,
    address: &Address,
    kind: ReadType,
) -> Option<ProgramValue> {
    get_version(memory, address, kind, None)
}

pub(in crate::kernel) fn get_at(
    point: &ProgramPoint,
    memory: &SymbolicMemory,
    address: &Address,
    kind: ReadType,
) -> Option<ProgramValue> {
    let version = match kind {
        ReadType::Integer(
            format @ (MachineIntegerType::Int8
            | MachineIntegerType::UInt8
            | MachineIntegerType::Int16
            | MachineIntegerType::UInt16
            | MachineIntegerType::Int32
            | MachineIntegerType::UInt32),
        ) => {
            let load_kind = LoadKind::of_type(format.program_type()).expect("indexed integer read");
            point
                .indexed_local_integer_version(address, load_kind)
                .and_then(|point| point.read_version_id())
        }
        _ => None,
    };
    get_version(memory, address, kind, version)
}

fn get_version(
    memory: &SymbolicMemory,
    address: &Address,
    kind: ReadType,
    version: Option<ProgramPointId>,
) -> Option<ProgramValue> {
    crate::instrumentation::record_deterministic_work(1);
    READS.with(|reads| {
        reads
            .borrow()
            .as_ref()?
            .get(&(
                crate::kernel::intern_memory_ref(memory),
                address.clone(),
                kind.key(),
                version,
            ))
            .cloned()
    })
}

/// A selected field, supplied by the resource-field evaluator. No ambient
/// resource or field search is needed to apply the preservation primitive.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FieldSelection {
    pub(crate) identity: Variable,
    pub(crate) index: usize,
}
thread_local! {
    static FIELD_SELECTION: std::cell::RefCell<Option<Result<Option<FieldSelection>, ()>>> = const { std::cell::RefCell::new(None) };
}

pub(crate) struct FieldScope(Option<Result<Option<FieldSelection>, ()>>);
impl FieldScope {
    pub(crate) fn enter() -> Self {
        Self(FIELD_SELECTION.with(|slot| slot.replace(Some(Ok(None)))))
    }
    pub(crate) fn selected(&self) -> Result<Option<FieldSelection>, &'static str> {
        FIELD_SELECTION.with(|slot| *slot.borrow().as_ref().unwrap())
            .map_err(|_| "preserve must select one resource field; split compound observations into explicit links")
    }
}
impl Drop for FieldScope {
    fn drop(&mut self) {
        FIELD_SELECTION.with(|slot| *slot.borrow_mut() = self.0.take());
    }
}
pub(crate) fn record_field(instance: &ResourceInstance, index: usize) {
    FIELD_SELECTION.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(selection) = slot.as_mut() else {
            return;
        };
        crate::instrumentation::record_deterministic_work(1);
        let current = FieldSelection {
            identity: instance.identity(),
            index,
        };
        match selection {
            Ok(None) => *selection = Ok(Some(current)),
            Ok(Some(previous)) if previous == &current => {}
            _ => *selection = Err(()),
        }
    });
}
