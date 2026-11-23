//! Prepared shared pointer transport across the selected immediate frame.
//! Existing native leaf checks own authority; no result survives this call.
use super::*;
use std::collections::HashMap;

struct Transport<'a> {
    after: &'a SymbolicMemory,
    assumptions: Option<(&'a PureFactContext, bool)>,
    reconstructed_word: bool,
    offsets: HashMap<SharedAddressOffset, SharedAddressOffset>,
    indices: HashMap<KernelTerm, SharedMachineIntegerTerm>,
    blocks: HashMap<SharedAddressBase, SharedAddressBase>,
}
impl<'a> Transport<'a> {
    fn new(
        after: &'a SymbolicMemory,
        assumptions: Option<(&'a PureFactContext, bool)>,
        reconstructed_word: bool,
    ) -> Self {
        Self {
            after,
            assumptions,
            reconstructed_word,
            offsets: Default::default(),
            indices: Default::default(),
            blocks: Default::default(),
        }
    }
    fn index(&mut self, root: &KernelTerm) -> Option<SharedMachineIntegerTerm> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(result) = self.indices.get(root) {
            return Some(result.clone());
        }
        let KernelType::Program(ty) = root.ty() else {
            return None;
        };
        let format = MachineIntegerType::from_program_type(*ty)?;
        let source =
            if let Some(source) = SharedMachineIntegerTerm::from_shared(format, root.clone()) {
                source
            } else if matches!(root.node(), KernelTermNode::Legacy(_)) {
                SharedMachineIntegerTerm::index(format, root.machine_conversion_leaf()?.clone())
            } else {
                return None;
            };
        let result = transport_framed_index(&source, self.after, self.assumptions)?;
        self.indices.insert(root.clone(), result.clone());
        Some(result)
    }
    fn offset(&mut self, root: &SharedAddressOffset) -> Option<SharedAddressOffset> {
        let mut pending = vec![(root, false)];
        while let Some((offset, finish)) = pending.pop() {
            if crate::kernel::assumptions::reasoning_interrupted() {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            if self.offsets.contains_key(offset) {
                continue;
            }
            let result = match offset.node() {
                KernelAddressOffset::Constant(_) | KernelAddressOffset::Variable(_) => {
                    offset.clone()
                }
                KernelAddressOffset::Add([left, right]) => {
                    if !finish {
                        pending.extend([(offset, true), (right, false), (left, false)]);
                        continue;
                    }
                    SharedAddressOffset::add(
                        self.offsets[left].clone(),
                        self.offsets[right].clone(),
                    )
                }
                KernelAddressOffset::Int32Scaled { value, byte_width }
                | KernelAddressOffset::Int64Scaled {
                    value, byte_width, ..
                } => {
                    let wide = match offset.node() {
                        KernelAddressOffset::Int64Scaled { unsigned, .. } => Some(*unsigned),
                        _ => None,
                    };
                    let index = self.index(value)?;
                    // One compatibility node, whose index stays shared. This
                    // reuses existing signed-extension/literal policy without
                    // materializing an address or numeric expression tree.
                    let leaf = transported_scaled_index(index, *byte_width, wide);
                    KernelAddressOffset::import(&leaf)
                }
            };
            self.offsets.insert(offset.clone(), result);
        }
        Some(self.offsets[root].clone())
    }
    fn address(&mut self, source: &SharedAddress) -> Option<SharedAddress> {
        let node = source.node();
        if self.reconstructed_word
            && let AddressBase::LoadedPointer(identity) = node.base.native_atom()
        {
            let (_, defining_address) = crate::kernel::eval::registered_pointer_load(*identity)?;
            let after = crate::kernel::intern_memory_ref(self.after);
            let target = Address::loaded_value(&after, &defining_address);
            let before = Address {
                base: node.base.native_atom().clone(),
                offset: AddressOffset::Constant(0),
            };
            // Both observations carry the same displacement. The selected
            // complete-word frame check is on their load identities, so it
            // needs no expansion of that unchanged displacement.
            if !self.assumptions.is_some_and(|(context, _)| {
                complete_pointer_reads_equal_across_frame(&before, &target, context)
            }) {
                return None;
            }
            return Some(SharedAddress::new(
                SharedAddressBase::import(&target.base),
                node.offset.clone(),
            ));
        }
        let block = if let Some(block) = self.blocks.get(&node.base) {
            block.clone()
        } else {
            // Only an atom crosses this existing leaf boundary. Its zero
            // offset neither exports nor inspects the shared displacement.
            let atom = Address {
                base: node.base.native_atom().clone(),
                offset: AddressOffset::Constant(0),
            };
            let result = transport_framed_atomic_pointer(&atom, self.after, self.assumptions)?;
            let block = SharedAddressBase::import(&result.base);
            self.blocks.insert(node.base.clone(), block.clone());
            block
        };
        let offset = self.offset(&node.offset)?;
        Some(if block == node.base && offset == node.offset {
            source.clone()
        } else {
            SharedAddress::new(block, offset)
        })
    }
}
impl PointerRewrite for Transport<'_> {
    type Error = ();
    fn numeric(&mut self, value: &KernelTerm) -> Result<KernelTerm, ()> {
        // Native complete-pointer transport maps addresses; it retains the
        // subobject width. Index transport is handled inside address().
        Ok(value.clone())
    }
    fn address(&mut self, value: &SharedAddress) -> Result<Option<SharedAddress>, ()> {
        Transport::address(self, value).map(Some).ok_or(())
    }
}

pub(super) fn transport_addresses(
    source: &[SharedAddress; 2],
    after: &SymbolicMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<[SharedAddress; 2]> {
    let mut transport = Transport::new(after, assumptions, false);
    Some([
        transport.address(&source[0])?,
        transport.address(&source[1])?,
    ])
}

pub(super) fn transport_offsets(
    source: &[SharedAddressOffset; 2],
    after: &SymbolicMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<[SharedAddressOffset; 2]> {
    let mut transport = Transport::new(after, assumptions, false);
    Some([transport.offset(&source[0])?, transport.offset(&source[1])?])
}

pub(crate) fn transport_address(
    source: &SharedAddress,
    after: &SymbolicMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedAddress> {
    source
        .try_rewrite(&mut Transport::new(after, assumptions, false))
        .ok()
}
pub(crate) fn transport_pointer(
    source: &SharedPointer,
    after: &SymbolicMemory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedPointer> {
    let reconstructed = matches!(
        source.node().address.node().offset.node(),
        KernelAddressOffset::Constant(0)
    ) && matches!(source.node().address.node().base.native_atom(), AddressBase::PureFunctionApplication(application) if application.integer_address_bits().is_some());
    source
        .try_rewrite(&mut Transport::new(after, assumptions, reconstructed))
        .ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    pub(super) fn fixture() -> (SharedMemory, Address, Address) {
        (
            intern_memory(
                SymbolicMemory::new()
                    .with_block("local:transport-source", 8)
                    .with_block("local:transport-other", 8),
            ),
            Address {
                base: AddressBase::Concrete("local:transport-source".into()),
                offset: AddressOffset::Constant(0),
            },
            Address {
                base: AddressBase::Concrete("local:transport-other".into()),
                offset: AddressOffset::Constant(0),
            },
        )
    }
    #[test]
    fn shared_transport_matches_native_index_policy_and_historical_reads() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        let changed = before
            .memory()
            .clone()
            .store(field.clone(), ProgramValue::Int32(MachineTerm::constant(3)));
        let context = PureFactContext::new();
        for wide in [None, Some(false), Some(true)] {
            let load = MachineTerm::MemoryLoad(
                ProgramPoint::at(&before),
                Box::new(field.clone()),
                if wide.is_some() {
                    LoadKind::Bits64
                } else {
                    LoadKind::Int32
                },
            );
            let scaled = match wide {
                None => AddressOffset::scaled_int32_node(load, 4),
                Some(unsigned) => AddressOffset::scaled_int64_node(load, 8, unsigned),
            };
            let source = Address {
                base: AddressBase::Symbolic(Variable(1007000)),
                offset: AddressOffset::Add(Box::new(scaled), Box::new(AddressOffset::Constant(0))),
            };
            let shared = SharedAddress::import(&source);
            let expected = transport_framed_atomic_pointer(&source, &after, Some((&context, true)))
                .expect("disjoint frame");
            let exports = KernelTermExport::machine_export_count();
            let output = transport_address(&shared, &after, Some((&context, true)))
                .expect("shared disjoint frame");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(output.export().unwrap(), expected);
            let expected =
                transport_framed_atomic_pointer(&source, &changed, Some((&context, true))).unwrap();
            let historical = transport_address(&shared, &changed, Some((&context, true)))
                .unwrap()
                .export()
                .unwrap();
            assert_eq!(historical, expected);
            let (AddressOffset::Int32Scaled { value, .. }
            | AddressOffset::Int64Scaled { value, .. }) = &historical.offset
            else {
                panic!("retained read index")
            };
            let (memory, _, _) = value.operand_view().read().expect("historical read");
            assert_eq!(memory, &before);
        }
    }
    #[test]
    fn shared_transport_keeps_native_constant_chain_and_carrier_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let after = SymbolicMemory::new();
        let cases = [
            AddressOffset::Add(
                Box::new(AddressOffset::Add(
                    Box::new(AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(1007020)),
                        4,
                    )),
                    Box::new(AddressOffset::Constant(2)),
                )),
                Box::new(AddressOffset::Constant(3)),
            ),
            AddressOffset::scaled_int32_node(MachineTerm::constant(u32::MAX), -4),
            AddressOffset::Int64Scaled {
                value: SharedMachineIntegerTerm::index(
                    MachineIntegerType::UInt64,
                    MachineTerm::Variable(Variable(1007021)),
                ),
                byte_width: 8,
                unsigned: true,
            },
            AddressOffset::scaled_int64_node(MachineTerm::uint64_constant(u64::MAX), 8, true),
        ];
        for offset in cases {
            let source = Address {
                base: AddressBase::Concrete("local:transport-shape".into()),
                offset,
            };
            let shared = SharedAddress::import(&source);
            let expected = transport_framed_atomic_pointer(&source, &after, None).unwrap();
            let output = transport_address(&shared, &after, None)
                .unwrap()
                .export()
                .unwrap();
            assert_eq!(output, expected);
        }
    }
    #[test]
    fn complete_transport_retains_metadata_and_original_bounds_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        let source = Pointer::new(
            Address::symbolic(Variable(1007010)),
            ProgramType::VoidPointer,
        )
        .with_bounds(Some(SubobjectBounds {
            start: field.clone(),
            width: MachineTerm::MemoryLoad(
                ProgramPoint::at(&before),
                Box::new(field),
                LoadKind::Int32,
            ),
        }));
        let shared = SharedPointer::import(&source);
        let output = transport_pointer(&shared, &after, None).unwrap();
        assert_eq!(output, shared);
        assert!(output.node().array.same_payload(&shared.node().array));
        assert_eq!(
            output.export().unwrap(),
            transport_framed_atomic_pointer_value(&source, &after, None).unwrap()
        );
    }
    #[test]
    fn displaced_reconstructions_keep_the_native_opaque_origin_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        let loaded = Arc::new(Address::loaded_value(&before, &field));
        let base = Address::from_integer_address(MachineTerm::MemoryLoad(
            ProgramPoint::at(&before),
            Box::new(field),
            LoadKind::Bits64,
        ));
        for offset in [
            AddressOffset::Constant(4),
            AddressOffset::Add(
                Box::new(AddressOffset::Constant(0)),
                Box::new(AddressOffset::Constant(0)),
            ),
        ] {
            let source = Pointer::new(
                Address {
                    base: base.base.clone(),
                    offset,
                },
                ProgramType::VoidPointer,
            )
            .with_provenance(loaded.clone())
            .with_bounds_owner(Some(loaded.clone()));
            assert!(source.address().integer_address_bits().is_none());
            let shared = SharedPointer::import(&source);
            let expected = transport_framed_atomic_pointer_value(&source, &after, None)
                .expect("ordinary origin requires no new complete-word evidence");
            let output = transport_pointer(&shared, &after, None).unwrap();
            assert_eq!(output.export().unwrap(), expected);
            assert_eq!(output.node().provenance, shared.node().provenance);
            assert_eq!(output.node().array.owner(), shared.node().array.owner());
        }
    }
    #[test]
    fn reconstructed_complete_word_uses_the_same_selected_frame_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        let loaded = Arc::new(Address::loaded_value(&before, &field));
        let source = Pointer::new(
            Address::from_integer_address(MachineTerm::MemoryLoad(
                ProgramPoint::at(&before),
                Box::new(field.clone()),
                LoadKind::Bits64,
            )),
            ProgramType::VoidPointer,
        )
        .with_provenance(loaded.clone())
        .with_bounds_owner(Some(loaded));
        let shared = SharedPointer::import(&source);
        let context = PureFactContext::new();
        let expected =
            transport_framed_atomic_pointer_value(&source, &after, Some((&context, true)));
        let output = transport_pointer(&shared, &after, Some((&context, true)));
        assert_eq!(
            output.as_ref().map(|value| value.export().unwrap()),
            expected
        );
        assert!(expected.is_some(), "complete word survives disjoint frame");
        assert!(transport_pointer(&shared, &after, None).is_none());
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/memory_history/shared_pointer_transport.rs");
}
