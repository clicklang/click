//! Prepared shared pointer transport across the selected immediate frame.
//! Existing native leaf checks own authority; no result survives this call.
use super::*;
use std::collections::HashMap;

struct Transport<'a> {
    after: &'a Memory,
    assumptions: Option<(&'a PureFactContext, bool)>,
    reconstructed_word: bool,
    offsets: HashMap<SharedPointerOffset, SharedPointerOffset>,
    constants: HashMap<SharedPointerOffset, Option<i64>>,
    indices: HashMap<KernelTerm, SharedMachineIntegerTerm>,
    blocks: HashMap<SharedPointerBlock, SharedPointerBlock>,
}
impl<'a> Transport<'a> {
    fn new(
        after: &'a Memory,
        assumptions: Option<(&'a PureFactContext, bool)>,
        reconstructed_word: bool,
    ) -> Self {
        Self {
            after,
            assumptions,
            reconstructed_word,
            offsets: Default::default(),
            constants: Default::default(),
            indices: Default::default(),
            blocks: Default::default(),
        }
    }
    fn constant(&mut self, value: i64) -> SharedPointerOffset {
        let result = KernelPointerOffset::Constant(value)
            .into_shared()
            .expect("constant offset");
        self.constants.insert(result.clone(), Some(value));
        result
    }
    fn add(
        &mut self,
        mut left: SharedPointerOffset,
        mut right: SharedPointerOffset,
    ) -> SharedPointerOffset {
        // Same constant/trailing-displacement policy as PointerOffsetTerm::add.
        // Child summaries come from this postorder walk, never a prefix scan.
        loop {
            crate::instrumentation::record_deterministic_work(1);
            let a = self.constants[&left];
            let b = self.constants[&right];
            if let (Some(a), Some(b)) = (a, b) {
                return self.constant(a + b);
            }
            if a == Some(0) {
                return right;
            }
            if b == Some(0) {
                return left;
            }
            if let (
                KernelPointerOffset::Add([base, trailing]),
                KernelPointerOffset::Constant(value),
            ) = (left.node(), right.node())
                && let Some(trailing) = self.constants[trailing]
            {
                let total = trailing + value;
                left = base.clone();
                right = self.constant(total);
                continue;
            }
            let result = KernelPointerOffset::Add([left, right])
                .into_shared()
                .expect("offset children");
            self.constants.insert(result.clone(), None);
            return result;
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
    fn offset(&mut self, root: &SharedPointerOffset) -> Option<SharedPointerOffset> {
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
                KernelPointerOffset::Constant(value) => {
                    self.constants.insert(offset.clone(), Some(*value));
                    offset.clone()
                }
                KernelPointerOffset::Variable(_) => {
                    self.constants.insert(offset.clone(), None);
                    offset.clone()
                }
                KernelPointerOffset::Add([left, right]) => {
                    if !finish {
                        pending.extend([(offset, true), (right, false), (left, false)]);
                        continue;
                    }
                    self.add(self.offsets[left].clone(), self.offsets[right].clone())
                }
                KernelPointerOffset::Int32Scaled { value, byte_width }
                | KernelPointerOffset::Int64Scaled {
                    value, byte_width, ..
                } => {
                    let wide = match offset.node() {
                        KernelPointerOffset::Int64Scaled { unsigned, .. } => Some(*unsigned),
                        _ => None,
                    };
                    let index = self.index(value)?;
                    // One compatibility node, whose index stays shared. This
                    // reuses existing signed-extension/literal policy without
                    // materializing an address or numeric expression tree.
                    let leaf = transported_scaled_index(index, *byte_width, wide);
                    let constant = leaf.as_const();
                    let result = KernelPointerOffset::import(&leaf);
                    self.constants.insert(result.clone(), constant);
                    result
                }
            };
            self.offsets.insert(offset.clone(), result);
        }
        Some(self.offsets[root].clone())
    }
    fn address(&mut self, source: &SharedPointerAddress) -> Option<SharedPointerAddress> {
        let node = source.node();
        if self.reconstructed_word
            && let PointerBlock::LoadedPointer(identity) = node.block.native_atom()
        {
            let (_, defining_address) = crate::kernel::eval::registered_pointer_load(*identity)?;
            let after = crate::kernel::intern_memory_ref(self.after);
            let target = Pointer::loaded_value(&after, &defining_address);
            let before = Pointer {
                block: node.block.native_atom().clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            // Both observations carry the same displacement. The selected
            // complete-word frame check is on their load identities, so it
            // needs no expansion of that unchanged displacement.
            if !self.assumptions.is_some_and(|(context, _)| {
                complete_pointer_reads_equal_across_frame(&before, &target, context)
            }) {
                return None;
            }
            return Some(SharedPointerAddress::new(
                SharedPointerBlock::import(&target.block),
                node.offset.clone(),
            ));
        }
        let block = if let Some(block) = self.blocks.get(&node.block) {
            block.clone()
        } else {
            // Only an atom crosses this existing leaf boundary. Its zero
            // offset neither exports nor inspects the shared displacement.
            let atom = Pointer {
                block: node.block.native_atom().clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let result = transport_framed_atomic_pointer(&atom, self.after, self.assumptions)?;
            let block = SharedPointerBlock::import(&result.block);
            self.blocks.insert(node.block.clone(), block.clone());
            block
        };
        let offset = self.offset(&node.offset)?;
        Some(if block == node.block && offset == node.offset {
            source.clone()
        } else {
            SharedPointerAddress::new(block, offset)
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
    fn address(
        &mut self,
        value: &SharedPointerAddress,
    ) -> Result<Option<SharedPointerAddress>, ()> {
        Transport::address(self, value).map(Some).ok_or(())
    }
}

pub(crate) fn transport_address(
    source: &SharedPointerAddress,
    after: &Memory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedPointerAddress> {
    source
        .try_rewrite(&mut Transport::new(after, assumptions, false))
        .ok()
}
pub(crate) fn transport_pointer(
    source: &SharedPointerValue,
    after: &Memory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedPointerValue> {
    let reconstructed = matches!(
        source.node().address.node().offset.node(),
        KernelPointerOffset::Constant(0)
    ) && matches!(source.node().address.node().block.native_atom(), PointerBlock::PureFunctionApplication(application) if application.integer_address_bits().is_some());
    source
        .try_rewrite(&mut Transport::new(after, assumptions, reconstructed))
        .ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    pub(super) fn fixture() -> (SharedMemory, Pointer, Pointer) {
        (
            intern_memory(
                Memory::new()
                    .with_block("local:transport-source", 8)
                    .with_block("local:transport-other", 8),
            ),
            Pointer {
                block: PointerBlock::Concrete("local:transport-source".into()),
                offset: PointerOffsetTerm::Constant(0),
            },
            Pointer {
                block: PointerBlock::Concrete("local:transport-other".into()),
                offset: PointerOffsetTerm::Constant(0),
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
                before.clone(),
                Box::new(field.clone()),
                if wide.is_some() {
                    LoadKind::Bits64
                } else {
                    LoadKind::Int32
                },
            );
            let scaled = match wide {
                None => PointerOffsetTerm::scaled_int32_node(load, 4),
                Some(unsigned) => PointerOffsetTerm::scaled_int64_node(load, 8, unsigned),
            };
            let source = Pointer {
                block: PointerBlock::Symbolic(Variable(1007000)),
                offset: PointerOffsetTerm::Add(
                    Box::new(scaled),
                    Box::new(PointerOffsetTerm::Constant(0)),
                ),
            };
            let shared = SharedPointerAddress::import(&source);
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
            let (PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. }) = &historical.offset
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
        let after = Memory::new();
        let cases = [
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::scaled_int32_node(
                        MachineTerm::Variable(Variable(1007020)),
                        4,
                    )),
                    Box::new(PointerOffsetTerm::Constant(2)),
                )),
                Box::new(PointerOffsetTerm::Constant(3)),
            ),
            PointerOffsetTerm::scaled_int32_node(MachineTerm::constant(u32::MAX), -4),
            PointerOffsetTerm::Int64Scaled {
                value: SharedMachineIntegerTerm::index(
                    MachineIntegerType::UInt64,
                    MachineTerm::Variable(Variable(1007021)),
                ),
                byte_width: 8,
                unsigned: true,
            },
            PointerOffsetTerm::scaled_int64_node(MachineTerm::uint64_constant(u64::MAX), 8, true),
        ];
        for offset in cases {
            let source = Pointer {
                block: PointerBlock::Concrete("local:transport-shape".into()),
                offset,
            };
            let shared = SharedPointerAddress::import(&source);
            let expected = transport_framed_atomic_pointer(&source, &after, None).unwrap();
            let output = transport_address(&shared, &after, None)
                .unwrap()
                .export()
                .unwrap();
            assert_eq!(output, expected);
        }
    }
    #[test]
    fn complete_transport_retains_metadata_and_original_extent_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let (before, field, other) = fixture();
        let after = before
            .memory()
            .clone()
            .store(other, ProgramValue::Int32(MachineTerm::constant(3)));
        let source = PointerValue::new(
            Pointer::symbolic(Variable(1007010)),
            ProgramType::VoidPointer,
        )
        .with_extent(Some(SubobjectExtent {
            start: field.clone(),
            width: MachineTerm::MemoryLoad(before, Box::new(field), LoadKind::Int32),
        }));
        let shared = SharedPointerValue::import(&source);
        let output = transport_pointer(&shared, &after, None).unwrap();
        assert_eq!(output, shared);
        assert!(Arc::ptr_eq(
            output.node().qualifiers.as_ref().unwrap(),
            shared.node().qualifiers.as_ref().unwrap()
        ));
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
        let loaded = Arc::new(Pointer::loaded_value(&before, &field));
        let base = Pointer::integer_address(MachineTerm::MemoryLoad(
            before,
            Box::new(field),
            LoadKind::Bits64,
        ));
        for offset in [
            PointerOffsetTerm::Constant(4),
            PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(0)),
                Box::new(PointerOffsetTerm::Constant(0)),
            ),
        ] {
            let source = PointerValue::new(
                Pointer {
                    block: base.block.clone(),
                    offset,
                },
                ProgramType::VoidPointer,
            )
            .with_designation(loaded.clone())
            .with_opaque_extent(Some(loaded.clone()));
            assert!(source.pointer().integer_address_bits().is_none());
            let shared = SharedPointerValue::import(&source);
            let expected = transport_framed_atomic_pointer_value(&source, &after, None)
                .expect("ordinary origin requires no new complete-word evidence");
            let output = transport_pointer(&shared, &after, None).unwrap();
            assert_eq!(output.export().unwrap(), expected);
            assert_eq!(output.node().designation, shared.node().designation);
            assert_eq!(output.node().opaque_extent, shared.node().opaque_extent);
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
        let loaded = Arc::new(Pointer::loaded_value(&before, &field));
        let source = PointerValue::new(
            Pointer::integer_address(MachineTerm::MemoryLoad(
                before,
                Box::new(field.clone()),
                LoadKind::Bits64,
            )),
            ProgramType::VoidPointer,
        )
        .with_designation(loaded.clone())
        .with_opaque_extent(Some(loaded));
        let shared = SharedPointerValue::import(&source);
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
    include!("../../scaling_tests/kernel/memory_provenance/shared_pointer_transport.rs");
}
