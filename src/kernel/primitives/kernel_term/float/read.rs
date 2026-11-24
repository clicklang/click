//! Typed float reads keep the producer's state and shared address.
use super::*;

impl KernelFloatType {
    pub(crate) fn load_kind(self) -> LoadKind {
        match self {
            Self::Float32 => LoadKind::Float32,
            Self::Float64 => LoadKind::Float64,
        }
    }
}

impl KernelTerm {
    pub(crate) fn float_read(
        format: KernelFloatType,
        point: ProgramPoint,
        address: SharedAddress,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::FloatRead(KernelMemoryRead::new(point, address)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn float_reads_keep_exact_states_widths_and_shared_addresses() {
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(SymbolicMemory::new())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(SymbolicMemory::new());
        let pointer = Address {
            base: AddressBase::Symbolic(Variable(999814)),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(999815)), 4),
        };
        let address = SharedAddress::import(&pointer);
        let mut identities = std::collections::HashSet::new();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            for memory in [&first, &second] {
                let source = MachineTerm::read_named(
                    ProgramPoint::at(memory),
                    Box::new(pointer.clone()),
                    format.load_kind(),
                );
                let root = KernelTermImport::default().float(format, &source);
                assert!(identities.insert(root.id()));
                assert!(!root.is_shared_machine_operand());
                let KernelTermNode::FloatRead(read) = root.node() else {
                    panic!("float read")
                };
                assert_eq!(read.parts().0.shared_memory().arena_id(), memory.arena_id());
                assert_eq!(read.parts().1, &address);
                assert_eq!(
                    root,
                    KernelTerm::float_read(
                        format,
                        crate::kernel::ProgramPoint::at(memory),
                        address.clone()
                    )
                );
                assert_eq!(
                    root.float_native_value(),
                    Some(&format.value(source.clone()))
                );
                assert!(root.0.machine_leaf.0.get().is_none());
                assert_eq!(
                    KernelTermExport::float(&root).unwrap(),
                    format.value(source)
                );
            }
        }
        // A malformed native carrier is preserved at its existing boundary,
        // rather than silently changing the written load kind during import.
        let mismatch = MachineTerm::read_named(
            ProgramPoint::at(&second),
            Box::new(pointer),
            LoadKind::Int32,
        );
        let root = KernelTermImport::default().float(KernelFloatType::Float32, &mismatch);
        assert!(matches!(root.node(), KernelTermNode::Legacy(_)));
        assert_eq!(
            KernelTermExport::float(&root).unwrap(),
            ProgramValue::Float32(mismatch)
        );
    }
}
