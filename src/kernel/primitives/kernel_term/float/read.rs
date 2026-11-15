//! Typed float reads keep the producer's snapshot and shared address.
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
        memory: SharedMemory,
        address: SharedPointerAddress,
    ) -> Self {
        Self::intern(
            KernelType::Program(format.program_type()),
            KernelTermNode::FloatRead(KernelSnapshotRead::new(memory, address)),
        )
    }

    /// Selected native read descriptor for remaining native readers. It never
    /// exports an enclosing expression or chooses a different snapshot.
    pub(crate) fn float_read_native(&self) -> Option<&MachineTerm> {
        let KernelTermNode::FloatRead(read) = self.node() else {
            return None;
        };
        let format = FloatOperandView::from_shared(self)?.format();
        let (memory, address) = read.parts();
        Some(self.0.machine_leaf.get_or_init(|| {
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(address.export().expect("float read address")),
                format.load_kind(),
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn float_reads_keep_exact_snapshots_widths_and_shared_addresses() {
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(Memory::new())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(Memory::new());
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(999814)),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(999815)),
                4,
            ),
        };
        let address = SharedPointerAddress::import(&pointer);
        let mut identities = std::collections::HashSet::new();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            for memory in [&first, &second] {
                let source = MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(pointer.clone()),
                    format.load_kind(),
                );
                let root = KernelTermImport::default().float(format, &source);
                assert!(identities.insert(root.id()));
                assert!(!root.is_shared_machine_operand());
                let KernelTermNode::FloatRead(read) = root.node() else {
                    panic!("float read")
                };
                assert_eq!(read.parts().0.arena_id(), memory.arena_id());
                assert_eq!(read.parts().1, &address);
                assert_eq!(
                    root,
                    KernelTerm::float_read(format, memory.clone(), address.clone())
                );
                assert_eq!(root.float_read_native(), Some(&source));
                assert_eq!(
                    KernelTermExport::float(&root).unwrap(),
                    format.value(source)
                );
                assert!(std::ptr::eq(
                    root.float_read_native().unwrap(),
                    root.float_read_native().unwrap()
                ));
            }
        }
        // A malformed native carrier is preserved at its existing boundary,
        // rather than silently changing the written load kind during import.
        let mismatch = MachineTerm::MemoryLoad(second, Box::new(pointer), LoadKind::Int32);
        let root = KernelTermImport::default().float(KernelFloatType::Float32, &mismatch);
        assert!(matches!(root.node(), KernelTermNode::Legacy(_)));
        assert_eq!(
            KernelTermExport::float(&root).unwrap(),
            ProgramValue::Float32(mismatch)
        );
    }
}
