//! Typed observations produced by logical reads. Consumers use these values,
//! never reconstruct their address/provenance from caches or memory history.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(in crate::kernel) enum ReadType {
    Pointer(CType),
    Abstract,
    PointerAddress,
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
            Self::Pointer(_) | Self::PointerAddress => C_POINTER_BYTE_WIDTH,
            Self::Abstract => ABSTRACT_VALUE_WIDTH,
            Self::Integer(format) => format.c_type().byte_width(),
        }
    }
}

type Reads = imbl::HashMap<(SharedCMemory, Pointer, ReadType), CValue>;
thread_local! {
    static READS: std::cell::RefCell<Option<Reads>> = const { std::cell::RefCell::new(None) };
}

/// Retain observations only while lowering and applying an explicit certificate.
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

pub(super) fn record(memory: &CMemory, address: &Pointer, value: &CValue) {
    if !READS.with(|reads| reads.borrow().is_some()) {
        return;
    }
    let value = value.numeric_value();
    let kind = match value {
        CValue::Pointer(p) => ReadType::Pointer(p.c_type()),
        CValue::Parameter(_) => ReadType::Abstract,
        CValue::Int32(_) => ReadType::Integer(MachineIntegerType::Int32),
        CValue::UInt32(_) => ReadType::Integer(MachineIntegerType::UInt32),
        CValue::UInt8(_) => ReadType::Integer(MachineIntegerType::UInt8),
        CValue::Int64(_) => ReadType::Integer(MachineIntegerType::Int64),
        CValue::UInt64(_) => ReadType::Integer(MachineIntegerType::UInt64),
        _ => return,
    };
    crate::instrumentation::record_deterministic_work(1);
    let kind = kind.key();
    let memory = crate::kernel::intern_c_memory_ref(memory);
    READS.with(|reads| {
        let mut slot = reads.borrow_mut();
        let reads = slot.as_mut().expect("active typed read scope");
        reads.insert((memory.clone(), address.clone(), kind), value.clone());
        if matches!(kind, ReadType::Pointer(_)) {
            reads.insert(
                (memory, address.clone(), ReadType::PointerAddress),
                value.clone(),
            );
        }
    });
}

/// Only the producer can file observations. A missing entry is not permission
/// to evaluate a read here. The written certificate names its reads by lowering
/// them before applying the primitive.
pub(in crate::kernel) fn get(
    memory: &CMemory,
    address: &Pointer,
    kind: ReadType,
) -> Option<CValue> {
    crate::instrumentation::record_deterministic_work(1);
    READS.with(|reads| {
        reads
            .borrow()
            .as_ref()?
            .get(&(
                crate::kernel::intern_c_memory_ref(memory),
                address.clone(),
                kind.key(),
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
