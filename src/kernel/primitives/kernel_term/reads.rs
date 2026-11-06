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
    /// Selected native read leaf for consumers still using the native atom
    /// interface. Never expands a surrounding shared arithmetic expression.
    pub(crate) fn machine_read_leaf(&self) -> Option<&MachineTerm> {
        let KernelTermNode::MemoryLoad {
            memory,
            address,
            kind,
        } = self.node()
        else {
            return None;
        };
        Some(self.0.machine_leaf.get_or_init(|| {
            MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), *kind)
        }))
    }

    pub(crate) fn scalar_read_descriptor(
        format: MachineIntegerType,
        memory: &SharedCMemory,
        address: &Pointer,
        kind: LoadKind,
    ) -> Option<Self> {
        let snapshots = address_snapshots(address)?;
        Some(Self::intern_key(NodeKey::with_read_snapshots(
            KernelType::C(format.c_type()),
            KernelTermNode::MemoryLoad {
                memory: memory.clone(),
                address: address.clone(),
                kind,
            },
            (!snapshots.is_empty()).then(|| snapshots.into()),
        )))
    }
}

/// Native pointer equality can omit auxiliary metadata in opaque machine
/// payloads. Do not use it to intern such a payload: those addresses retain
/// the producer-local legacy boundary until their own shared forms migrate.
/// Retain arena identities for every nested read: native snapshot equality
/// otherwise compares memory contents across arenas. The ordered identities
/// let the interner refuse that comparison before inspecting the address.
pub(super) fn address_snapshots(address: &Pointer) -> Option<Vec<(u32, u32)>> {
    enum Input<'a> {
        Offset(&'a PointerOffsetTerm),
        Word(&'a MachineTerm),
    }
    let mut pending = vec![Input::Offset(&address.offset)];
    let mut snapshots = Vec::new();
    while let Some(input) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match input {
            Input::Offset(offset) => match offset {
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                PointerOffsetTerm::Add(a, b) => {
                    pending.extend([Input::Offset(b), Input::Offset(a)]);
                }
                PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } => {
                    pending.push(Input::Word(value));
                }
            },
            Input::Word(word) => match word {
                MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
                MachineTerm::Binary { left, right, .. } => {
                    pending.extend([Input::Word(right), Input::Word(left)]);
                }
                MachineTerm::Unary { operand, .. } => pending.push(Input::Word(operand)),
                MachineTerm::Cast { value, .. } => pending.push(Input::Word(value)),
                MachineTerm::MemoryLoad(memory, address, _) => {
                    snapshots.push(memory.arena_id());
                    pending.push(Input::Offset(&address.offset));
                }
                _ => return None,
            },
        }
    }
    Some(snapshots)
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
            assert!(term.is_shared_machine_operand());
            crate::kernel::eval::clear_load_variable_registry();
            assert_eq!(
                crate::kernel::MachineOperandView::Shared(&term)
                    .read_source()
                    .as_deref(),
                Some(&native)
            );
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
        let term = crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap();
        assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
        assert_eq!(
            term,
            KernelTermImport::default().machine(format, &descriptor)
        );
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }
    #[test]
    fn named_read_import_and_arithmetic_storage_retain_the_same_descriptor() {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let raw = MachineTerm::MemoryLoad(
            intern_c_memory(CMemory::new()),
            Box::new(Pointer::symbolic(Variable(993126))),
            LoadKind::UInt32,
        );
        let (name, descriptor) = crate::kernel::eval::load_variable_for_term(&raw).unwrap();
        let named = MachineTerm::Variable(name);
        let arithmetic = KernelTermImport::default()
            .machine_arithmetic(format, &named)
            .unwrap();
        let general = KernelTermImport::default().machine(format, &named);
        assert_eq!(general, arithmetic);
        assert_eq!(KernelTermExport::machine(&general).unwrap(), descriptor);
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(
            KernelTermImport::default().machine(format, &descriptor),
            general
        );
        assert_eq!(KernelTermExport::machine(&arithmetic).unwrap(), descriptor);
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
        let term = crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap();
        let registry = crate::kernel::eval::capture_load_variable_registry();
        crate::kernel::eval::clear_load_variable_registry();
        assert!(crate::kernel::eval::registered_scalar_read_term(&name, format).is_none());
        crate::kernel::eval::restore_load_variable_registry(&registry);
        assert_eq!(
            crate::kernel::eval::registered_scalar_read_term(&name, format).unwrap(),
            term
        );
        assert_eq!(KernelTermExport::machine(&term).unwrap(), descriptor);
    }

    #[test]
    fn nested_scalar_reads_retain_both_snapshots_without_registered_names() {
        let _session = VerificationSession::enter();
        let p = Pointer::symbolic(Variable(993140));
        let before = intern_c_memory(CMemory::new());
        let after = intern_c_memory(
            CMemory::new().store(p.clone(), CValue::Int32(MachineTerm::constant(1))),
        );
        let nested = |inner: SharedCMemory, outer: SharedCMemory, kind| {
            MachineTerm::MemoryLoad(
                outer,
                Box::new(Pointer {
                    block: PointerBlock::Symbolic(Variable(993141)),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(MachineTerm::MemoryLoad(inner, Box::new(p.clone()), kind)),
                        byte_width: 4,
                    },
                }),
                LoadKind::Int32,
            )
        };
        let raw = nested(before.clone(), after.clone(), LoadKind::Int32);
        let term = KernelTermImport::default().machine(MachineIntegerType::Int32, &raw);
        assert!(matches!(term.node(), KernelTermNode::MemoryLoad { .. }));
        for other in [
            nested(after.clone(), after.clone(), LoadKind::Int32),
            nested(before.clone(), before.clone(), LoadKind::Int32),
            nested(before, after, LoadKind::UInt32),
        ] {
            assert_ne!(
                term,
                KernelTermImport::default().machine(MachineIntegerType::Int32, &other)
            );
        }
        crate::kernel::eval::clear_load_variable_registry();
        assert_eq!(KernelTermExport::machine(&term).unwrap(), raw);
        assert_eq!(
            term,
            KernelTermImport::default().machine(MachineIntegerType::Int32, &raw)
        );
    }

    #[test]
    fn nested_read_identity_does_not_compare_snapshot_contents_across_arenas() {
        let first = {
            let _session = VerificationSession::enter();
            intern_c_memory(CMemory::new())
        };
        let _session = VerificationSession::enter();
        let second = intern_c_memory(CMemory::new());
        assert_ne!(first.arena_id(), second.arena_id());
        assert_eq!(first, second); // Same contents, distinct snapshot identities.
        let outer = second.clone();
        let import = |inner| {
            KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &MachineTerm::MemoryLoad(
                    outer.clone(),
                    Box::new(Pointer {
                        block: PointerBlock::Symbolic(Variable(993151)),
                        offset: PointerOffsetTerm::Int32Scaled {
                            value: Box::new(MachineTerm::MemoryLoad(
                                inner,
                                Box::new(Pointer::symbolic(Variable(993150))),
                                LoadKind::Int32,
                            )),
                            byte_width: 4,
                        },
                    }),
                    LoadKind::Int32,
                ),
            )
        };
        let first_term = import(first.clone());
        let second_term = import(second);
        assert!(matches!(
            first_term.node(),
            KernelTermNode::MemoryLoad { .. }
        ));
        assert_ne!(first_term, second_term);
        assert_eq!(first_term, import(first));
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
