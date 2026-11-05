//! Exact read terms at the native/shared boundary. This does not choose a
//! memory version, follow an alias, or read a stored value.
use super::*;

impl KernelTermImport {
    pub(super) fn scalar_read(
        &mut self,
        format: MachineIntegerType,
        value: &MachineTerm,
    ) -> Option<KernelTerm> {
        match value {
            MachineTerm::MemoryLoad(memory, address, kind) => {
                KernelTerm::scalar_read_descriptor(format, memory, address, *kind)
            }
            MachineTerm::Variable(variable) if crate::kernel::eval::is_load_variable(variable) => {
                crate::kernel::eval::registered_scalar_read_term(variable, format)
            }
            _ => None,
        }
    }
}

impl KernelTerm {
    pub(crate) fn scalar_read_descriptor(
        format: MachineIntegerType,
        memory: &SharedCMemory,
        address: &Pointer,
        kind: LoadKind,
    ) -> Option<Self> {
        if !exact_address(address) {
            return None;
        }
        Some(Self::intern(
            KernelType::C(format.c_type()),
            KernelTermNode::MemoryLoad {
                memory: memory.clone(),
                address: address.clone(),
                kind,
            },
        ))
    }
}

/// Native pointer equality can omit auxiliary metadata in opaque machine
/// payloads. Do not use it to intern such a payload: those addresses retain
/// the producer-local legacy boundary until their own shared forms migrate.
fn exact_address(address: &Pointer) -> bool {
    let mut offsets = vec![&address.offset];
    let mut words = Vec::new();
    while let Some(offset) = offsets.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
            PointerOffsetTerm::Add(a, b) => offsets.extend([a.as_ref(), b.as_ref()]),
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => words.push(value.as_ref()),
        }
    }
    while let Some(word) = words.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match word {
            MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
            MachineTerm::Binary { left, right, .. } => {
                words.extend([left.as_ref(), right.as_ref()])
            }
            MachineTerm::Unary { operand, .. } => words.push(operand),
            MachineTerm::Cast { value, .. } => words.push(value),
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::VerificationSession;

    #[test]
    fn scalar_reads_retain_exact_descriptors_and_survive_registry_reset() {
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(993100));
        let memory = intern_c_memory(
            CMemory::new().store(address.clone(), CValue::Int32(MachineTerm::constant(7))),
        );
        for (kind, format) in [
            (LoadKind::Int8, MachineIntegerType::Int8),
            (LoadKind::UInt8, MachineIntegerType::UInt8),
            (LoadKind::Int16, MachineIntegerType::Int16),
            (LoadKind::UInt16, MachineIntegerType::UInt16),
            (LoadKind::Int32, MachineIntegerType::Int32),
            (LoadKind::UInt32, MachineIntegerType::UInt32),
            (LoadKind::Bits64, MachineIntegerType::UInt64),
            (LoadKind::Int128, MachineIntegerType::Int128),
            (LoadKind::UInt128, MachineIntegerType::UInt128),
        ] {
            let native = MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), kind);
            let term = KernelTermImport::default().machine(format, &native);
            assert!(
                matches!(term.node(), KernelTermNode::MemoryLoad { memory: m, address: p, kind: k } if m == &memory && p == &address && *k == kind)
            );
            assert!(
                !term.is_shared_machine_operand(),
                "checker consumers must migrate before admission"
            );
            crate::kernel::eval::clear_load_variable_registry();
            assert_eq!(KernelTermExport::machine(&term).unwrap(), native);
            assert_eq!(KernelTermImport::default().machine(format, &native), term);
        }
    }

    #[test]
    fn scalar_read_identity_distinguishes_snapshot_address_and_kind() {
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(993110));
        let memory = intern_c_memory(CMemory::new());
        let written = intern_c_memory(
            CMemory::new().store(address.clone(), CValue::Int32(MachineTerm::constant(7))),
        );
        let load = |memory, address, kind| {
            KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &MachineTerm::MemoryLoad(memory, Box::new(address), kind),
            )
        };
        let first = load(memory.clone(), address.clone(), LoadKind::Int32);
        assert_ne!(first, load(written, address.clone(), LoadKind::Int32));
        assert_ne!(
            first,
            load(
                memory.clone(),
                Pointer::symbolic(Variable(993111)),
                LoadKind::Int32
            )
        );
        assert_ne!(first, load(memory, address, LoadKind::UInt32));
    }

    #[test]
    fn registered_read_handle_imports_as_its_owned_read_descriptor() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let raw = MachineTerm::MemoryLoad(
            intern_c_memory(CMemory::new()),
            Box::new(Pointer::symbolic(Variable(993120))),
            LoadKind::Int32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let term = KernelTermImport::default().machine(format, &MachineTerm::Variable(name));
        assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
        assert_eq!(
            term,
            KernelTermImport::default().machine(format, &descriptor)
        );
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }
    #[test]
    fn registered_read_cache_follows_registry_capture_and_restore() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let raw = MachineTerm::MemoryLoad(
            intern_c_memory(CMemory::new()),
            Box::new(Pointer::symbolic(Variable(993125))),
            LoadKind::Int32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let named = MachineTerm::Variable(name);
        let term = KernelTermImport::default().machine(format, &named);
        let registry = crate::kernel::eval::capture_load_variable_registry();
        crate::kernel::eval::clear_load_variable_registry();
        assert!(crate::kernel::eval::registered_scalar_read_term(&name, format).is_none());
        crate::kernel::eval::restore_load_variable_registry(&registry);
        assert_eq!(KernelTermImport::default().machine(format, &named), term);
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }

    #[test]
    fn read_addresses_outside_the_shared_fragment_keep_the_exact_legacy_payload() {
        let _session = VerificationSession::enter();
        let address = Pointer {
            block: PointerBlock::Symbolic(Variable(993130)),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(MachineTerm::IntegerToMachine {
                    value: IntegerTerm::Variable(Variable(993131)).into(),
                    destination: MachineIntegerType::Int32,
                }),
                byte_width: 4,
            },
        };
        let native = MachineTerm::MemoryLoad(
            intern_c_memory(CMemory::new()),
            Box::new(address),
            LoadKind::Int32,
        );
        let term = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        assert!(matches!(term.node(), KernelTermNode::Legacy(_)));
        assert_eq!(KernelTermExport::machine(&term).unwrap(), native);
    }
}
