//! Prepared shared pointer transport across the selected immediate frame.
//! Existing native leaf checks own authority; no result survives this call.
use super::*;
use std::collections::HashMap;

struct Transport<'a> {
    after: &'a ProgramPoint,
    assumptions: Option<(&'a PureFactContext, bool)>,
    reconstructed_word: bool,
    offsets: HashMap<SharedAddressOffset, SharedAddressOffset>,
    indices: HashMap<KernelTerm, SharedMachineIntegerTerm>,
    blocks: HashMap<SharedAddressBase, SharedAddressBase>,
}
impl<'a> Transport<'a> {
    fn new(
        after: &'a ProgramPoint,
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
        let source = SharedMachineIntegerTerm::from_shared(format, root.clone())?;
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
                    leaf.into_shared()
                }
            };
            self.offsets.insert(offset.clone(), result);
        }
        Some(self.offsets[root].clone())
    }
    fn address(&mut self, source: &SharedAddress) -> Option<SharedAddress> {
        let node = source.node();
        if self.reconstructed_word
            && let AddressBase::Load(load) = node.base.native_atom()
        {
            let after = self.after.shared_memory().clone();
            let target = OldAddress::loaded_value(&after, load.cell());
            let before = OldAddress {
                base: node.base.native_atom().clone(),
                offset: AddressOffset::constant(0),
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
            let atom = OldAddress {
                base: node.base.native_atom().clone(),
                offset: AddressOffset::constant(0),
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
    after: &ProgramPoint,
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
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<[SharedAddressOffset; 2]> {
    let mut transport = Transport::new(after, assumptions, false);
    Some([transport.offset(&source[0])?, transport.offset(&source[1])?])
}

pub(crate) fn transport_address(
    source: &SharedAddress,
    after: &ProgramPoint,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedAddress> {
    source
        .try_rewrite(&mut Transport::new(after, assumptions, false))
        .ok()
}
pub(crate) fn transport_pointer(
    source: &SharedPointer,
    after: &ProgramPoint,
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
    pub(super) fn fixture() -> (SharedMemory, OldAddress, OldAddress) {
        (
            intern_memory(
                SymbolicMemory::new()
                    .with_block("local:transport-source", 8)
                    .with_block("local:transport-other", 8),
            ),
            OldAddress {
                base: AddressBase::Concrete("local:transport-source".into()),
                offset: AddressOffset::constant(0),
            },
            OldAddress {
                base: AddressBase::Concrete("local:transport-other".into()),
                offset: AddressOffset::constant(0),
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
            .store(other, ProgramValue::Int32(OldMachineTerm::constant(3)));
        let changed = before.memory().clone().store(
            field.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(3)),
        );
        let context = PureFactContext::new();
        for wide in [None, Some(false), Some(true)] {
            let load = OldMachineTerm::read_named(
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
            let source = OldAddress {
                base: AddressBase::Symbolic(Variable(1007000)),
                offset: AddressOffset::raw_add(scaled, AddressOffset::constant(0)),
            };
            let shared = SharedAddress::import(&source);
            let expected = transport_framed_atomic_pointer(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&after),
                Some((&context, true)),
            )
            .expect("disjoint frame");
            let exports = KernelTermExport::machine_export_count();
            let output = transport_address(
                &shared,
                &crate::kernel::ProgramPoint::of_memory(&after),
                Some((&context, true)),
            )
            .expect("shared disjoint frame");
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(output.export().unwrap(), expected);
            let expected = transport_framed_atomic_pointer(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&changed),
                Some((&context, true)),
            )
            .unwrap();
            let historical = transport_address(
                &shared,
                &crate::kernel::ProgramPoint::of_memory(&changed),
                Some((&context, true)),
            )
            .unwrap()
            .export()
            .unwrap();
            assert_eq!(historical, expected);
            let (crate::kernel::OffsetView::Int32Scaled { index: value, .. }
            | crate::kernel::OffsetView::Int64Scaled { index: value, .. }) =
                historical.offset.clone().view()
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
            AddressOffset::raw_add(
                AddressOffset::raw_add(
                    AddressOffset::scaled_int32_node(
                        OldMachineTerm::Variable(Variable(1007020)),
                        4,
                    ),
                    AddressOffset::constant(2),
                ),
                AddressOffset::constant(3),
            ),
            AddressOffset::scaled_int32_node(OldMachineTerm::constant(u32::MAX), -4),
            AddressOffset::int64_scaled(
                SharedMachineIntegerTerm::index(
                    MachineIntegerType::UInt64,
                    OldMachineTerm::Variable(Variable(1007021)),
                ),
                8,
                true,
            ),
            AddressOffset::scaled_int64_node(OldMachineTerm::uint64_constant(u64::MAX), 8, true),
        ];
        for offset in cases {
            let source = OldAddress {
                base: AddressBase::Concrete("local:transport-shape".into()),
                offset: offset,
            };
            let shared = SharedAddress::import(&source);
            let expected = transport_framed_atomic_pointer(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
            .unwrap();
            let output = transport_address(
                &shared,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
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
            .store(other, ProgramValue::Int32(OldMachineTerm::constant(3)));
        let source = OldPointer::new(
            OldAddress::symbolic(Variable(1007010)),
            ProgramType::VoidPointer,
        )
        .with_bounds(Some(SubobjectBounds {
            start: field.clone(),
            width: OldMachineTerm::read_named(
                ProgramPoint::at(&before),
                Box::new(field),
                LoadKind::Int32,
            ),
        }));
        let shared = SharedPointer::import(&source);
        let output = transport_pointer(
            &shared,
            &crate::kernel::ProgramPoint::of_memory(&after),
            None,
        )
        .unwrap();
        assert_eq!(output, shared);
        assert!(output.node().array.same_payload(&shared.node().array));
        assert_eq!(
            output.export().unwrap(),
            transport_framed_atomic_pointer_value(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None
            )
            .unwrap()
        );
    }
    #[test]
    fn displaced_reconstructions_keep_the_native_opaque_origin_policy() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(OldMachineTerm::constant(3)));
        let loaded = Arc::new(OldAddress::loaded_value(&before, &field));
        let base = OldAddress::from_integer_address(OldMachineTerm::read_named(
            ProgramPoint::at(&before),
            Box::new(field),
            LoadKind::Bits64,
        ));
        for offset in [
            AddressOffset::constant(4),
            AddressOffset::raw_add(AddressOffset::constant(0), AddressOffset::constant(0)),
        ] {
            let source = OldPointer::new(
                OldAddress {
                    base: base.base.clone(),
                    offset: offset,
                },
                ProgramType::VoidPointer,
            )
            .with_provenance(loaded.clone())
            .with_bounds_owner(Some(loaded.clone()));
            assert!(source.address().integer_address_bits().is_none());
            let shared = SharedPointer::import(&source);
            let expected = transport_framed_atomic_pointer_value(
                &source,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
            .expect("ordinary origin requires no new complete-word evidence");
            let output = transport_pointer(
                &shared,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None,
            )
            .unwrap();
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
            .store(other, ProgramValue::Int32(OldMachineTerm::constant(3)));
        let loaded = Arc::new(OldAddress::loaded_value(&before, &field));
        let source = OldPointer::new(
            OldAddress::from_integer_address(OldMachineTerm::read_named(
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
        let expected = transport_framed_atomic_pointer_value(
            &source,
            &crate::kernel::ProgramPoint::of_memory(&after),
            Some((&context, true)),
        );
        let output = transport_pointer(
            &shared,
            &crate::kernel::ProgramPoint::of_memory(&after),
            Some((&context, true)),
        );
        assert_eq!(
            output.as_ref().map(|value| value.export().unwrap()),
            expected
        );
        assert!(expected.is_some(), "complete word survives disjoint frame");
        assert!(
            transport_pointer(
                &shared,
                &crate::kernel::ProgramPoint::of_memory(&after),
                None
            )
            .is_none()
        );
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/memory_history/shared_pointer_transport.rs");
}
