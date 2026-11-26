//! Shallow offset keys retain shared graphs. These are identities/selectors,
//! not evidence; state erasure still requires the existing checked bridge.
use super::*;
use crate::kernel::{
    KernelAddressOffset as O, MachineOperandView as V, SharedAddress, SharedAddressOffset,
    SharedPointer,
};
use std::sync::{Mutex, OnceLock};

type Table<N> = Mutex<HashMap<u64, Vec<Weak<Record<N>>>>>;
pub(crate) trait KeyNode: Eq + Hash + Sized + 'static {
    fn table() -> &'static Table<Self>;
    fn checked_match(&self) -> bool {
        false
    }
}
pub(crate) struct Record<N: KeyNode> {
    id: u64,
    fingerprint: u64,
    node: N,
    checked: bool,
}
pub(crate) struct Canonical<N: KeyNode>(Arc<Record<N>>);
impl<N: KeyNode> Clone for Canonical<N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<N: KeyNode> fmt::Debug for Canonical<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PointerKey").field(&self.0.id).finish()
    }
}
impl<N: KeyNode> PartialEq for Canonical<N> {
    fn eq(&self, b: &Self) -> bool {
        self.0.id == b.0.id
    }
}
impl<N: KeyNode> Eq for Canonical<N> {}
impl<N: KeyNode> PartialOrd for Canonical<N> {
    fn partial_cmp(&self, b: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(b))
    }
}
impl<N: KeyNode> Ord for Canonical<N> {
    fn cmp(&self, b: &Self) -> std::cmp::Ordering {
        self.0.id.cmp(&b.0.id)
    }
}
impl<N: KeyNode> Hash for Canonical<N> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        // Some selectors retain only a fingerprint, not this key handle.
        // Keep that fingerprint stable after the last live key is dropped.
        self.0.fingerprint.hash(h)
    }
}
impl<N: KeyNode> Drop for Record<N> {
    fn drop(&mut self) {
        let Ok(mut table) = N::table().try_lock() else {
            return;
        };
        if let Some(bucket) = table.get_mut(&self.fingerprint) {
            bucket.retain(|entry| entry.strong_count() != 0);
            if bucket.is_empty() {
                table.remove(&self.fingerprint);
            }
        }
    }
}
impl<N: KeyNode> Canonical<N> {
    pub(super) fn new(node: N) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(1);
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        node.hash(&mut hash);
        let fingerprint = hash.finish();
        let mut table = N::table().lock().expect("pointer key interner");
        let bucket = table.entry(fingerprint).or_default();
        if let Some(record) = bucket
            .iter()
            .filter_map(Weak::upgrade)
            .find(|record| record.node == node)
        {
            return Self(record);
        }
        bucket.retain(|entry| entry.strong_count() != 0);
        let checked = node.checked_match();
        let record = Arc::new(Record {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            fingerprint,
            node,
            checked,
        });
        bucket.push(Arc::downgrade(&record));
        Self(record)
    }
    #[cfg(test)]
    pub(super) fn node(&self) -> &N {
        &self.0.node
    }
    pub(super) fn requires_checked_match(&self) -> bool {
        self.0.checked
    }
}
impl KeyNode for MemoryErasedAddressOffsetNode {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<MemoryErasedAddressOffsetNode>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
    fn checked_match(&self) -> bool {
        self.requires_checked_match()
    }
}
impl KeyNode for AlphaPointerOffsetNode {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<AlphaPointerOffsetNode>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
}
impl KeyNode for AlphaMachineKey {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<AlphaMachineKey>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
}

/// The memo belongs to this one lexical scope, never to an ambient fact set.
fn offsets<K: Clone>(
    root: &SharedAddressOffset,
    mut build: impl FnMut(&O, Option<[K; 2]>) -> Option<K>,
) -> Option<K> {
    let mut memo: HashMap<SharedAddressOffset, K> = HashMap::new();
    let mut pending = vec![(root.clone(), false)];
    while let Some((offset, finish)) = pending.pop() {
        if memo.contains_key(&offset) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        if let O::Add(children) = offset.node()
            && !finish
        {
            pending.push((offset.clone(), true));
            pending.extend(children.iter().rev().cloned().map(|child| (child, false)));
            continue;
        }
        let children = if let O::Add([a, b]) = offset.node() {
            Some([memo[a].clone(), memo[b].clone()])
        } else {
            None
        };
        let key = build(offset.node(), children)?;
        memo.insert(offset, key);
    }
    memo.remove(root)
}

#[allow(dead_code)] // Prepared before the pointer-producing boundaries switch.
pub(super) fn state_offset(root: &SharedAddressOffset) -> MemoryErasedAddressOffsetKey {
    offsets(root, |node, children| {
        Some(Canonical::new(match node {
            O::Constant(value) => {
                MemoryErasedAddressOffsetNode::Exact(AddressOffset::constant(*value))
            }
            O::Variable(value) => {
                MemoryErasedAddressOffsetNode::Exact(AddressOffset::variable(*value))
            }
            O::Add(_) => {
                let [a, b] = children.unwrap();
                MemoryErasedAddressOffsetNode::Add(a, b)
            }
            O::Int32Scaled { value, byte_width } => MemoryErasedAddressOffsetNode::Int32Scaled {
                value: memory_operands::operand(V::Shared(value)),
                byte_width: *byte_width,
            },
            O::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => MemoryErasedAddressOffsetNode::Int64Scaled {
                value: memory_operands::operand(V::Shared(value)),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }))
    })
    .expect("state key is total")
}

#[allow(dead_code)]
pub(super) fn alpha_offset<const ALLOW_LOADS: bool>(
    root: &SharedAddressOffset,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaAddressOffsetKey> {
    enum Frame {
        Visit(SharedAddressOffset),
        Add(SharedAddressOffset, usize),
    }
    // Registry definitions can contain local binders. Like the native load
    // memo, retain both the entry ordinal and the resulting ordinal.
    let mut memo: HashMap<(SharedAddressOffset, usize), (AlphaAddressOffsetKey, usize)> =
        HashMap::new();
    let mut numeric: HashMap<(u64, usize), Canonical<AlphaMachineKey>> = HashMap::new();
    let mut pending = vec![Frame::Visit(root.clone())];
    let mut values = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Add(offset, before) => {
                let b = values.pop()?;
                let a = values.pop()?;
                let key = Canonical::new(AlphaPointerOffsetNode::Add(a, b));
                memo.insert((offset, before), (key.clone(), *next));
                values.push(key);
            }
            Frame::Visit(offset) => {
                alpha_work_checkpoint(bindings, 1)?;
                let before = *next;
                if let Some((key, after)) = memo.get(&(offset.clone(), before)) {
                    *next = *after;
                    values.push(key.clone());
                    continue;
                }
                let node = match offset.node() {
                    O::Add([a, b]) => {
                        pending.push(Frame::Add(offset.clone(), before));
                        pending.push(Frame::Visit(b.clone()));
                        pending.push(Frame::Visit(a.clone()));
                        continue;
                    }
                    O::Constant(value) => AlphaPointerOffsetNode::Constant(*value),
                    O::Variable(variable) => {
                        let key = alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
                            &AddressOffset::variable(*variable),
                            bindings,
                            next,
                        )?;
                        memo.insert((offset, before), (key.clone(), *next));
                        values.push(key);
                        continue;
                    }
                    O::Int32Scaled { value, byte_width }
                    | O::Int64Scaled {
                        value, byte_width, ..
                    } => {
                        let cache = (value.id(), *next);
                        let key = match numeric.get(&cache) {
                            Some(key) => key.clone(),
                            None => {
                                let key = Canonical::new(alpha_machine_key::<ALLOW_LOADS>(
                                    V::Shared(value),
                                    bindings,
                                    next,
                                )?);
                                numeric.insert(cache, key.clone());
                                key
                            }
                        };
                        match offset.node() {
                            O::Int64Scaled { unsigned, .. } => {
                                AlphaPointerOffsetNode::Int64Scaled {
                                    value: key,
                                    byte_width: *byte_width,
                                    unsigned: *unsigned,
                                }
                            }
                            _ => AlphaPointerOffsetNode::Int32Scaled {
                                value: key,
                                byte_width: *byte_width,
                            },
                        }
                    }
                };
                let key = Canonical::new(node);
                memo.insert((offset, before), (key.clone(), *next));
                values.push(key);
            }
        }
    }
    values.pop()
}

#[allow(dead_code)]
pub(super) fn state_address(pointer: &SharedAddress) -> MemoryErasedAddressKey {
    let depth = POINTER_READ_KEY_DEPTH.with(|depth| depth.replace(depth.get() + 1));
    let _restore = PointerReadKeyDepth(depth);
    let block = pointer.node().base.native_atom();
    // Existing depth bound and registry authority; never export the offset.
    let read = match block {
        AddressBase::Load(_) if depth < 3 => OldAddress {
            base: block.clone(),
            offset: AddressOffset::constant(0),
        }
        .as_loaded_value()
        .map(|read| read.defining_address),
        AddressBase::Symbolic(variable) if depth < 3 => {
            crate::kernel::registered_load_for_variable(variable).map(|(_, source)| source)
        }
        _ => None,
    };
    MemoryErasedAddressKey {
        base: read
            .map(|source| {
                MemoryErasedAddressBaseKey::Read(Box::new(memory_erased_address_key(&source)))
            })
            .unwrap_or_else(|| MemoryErasedAddressBaseKey::Exact(block.clone())),
        offset: Box::new(state_offset(&pointer.node().offset)),
    }
}
#[allow(dead_code)]
pub(super) fn alpha_address<const ALLOW_LOADS: bool>(
    pointer: &SharedAddress,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaAddressKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(AlphaAddressKey {
        base: alpha_address_base_key::<ALLOW_LOADS>(
            pointer.node().base.native_atom(),
            bindings,
            next,
        )?,
        offset: alpha_offset::<ALLOW_LOADS>(&pointer.node().offset, bindings, next)?,
    })
}
#[allow(dead_code)]
pub(super) fn recorded_value(pointer: &SharedPointer) -> MemoryErasedPointerKey {
    let p = pointer.node();
    let known = p.array.is_known();
    MemoryErasedPointerKey {
        address: state_address(&p.address),
        provenance: state_address(&p.provenance),
        bounds_owner: p.array.opaque_owner().map(state_address),
        bounds: p.array.bounds().map(|e| {
            (
                state_address(&e.start),
                memory_operands::operand(V::Shared(&e.width)),
            )
        }),
        bounds_known: known,
    }
}

#[allow(dead_code)]
pub(super) fn alpha_value<const ALLOW_LOADS: bool>(
    pointer: &SharedPointer,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaProgramValueKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let p = pointer.node();
    Some(AlphaProgramValueKey::Pointer {
        pointer: alpha_address::<ALLOW_LOADS>(&p.address, bindings, next)?,
        provenance: alpha_address::<ALLOW_LOADS>(&p.provenance, bindings, next)?,
        bounds_known: p.array.is_known(),
        bounds_owner: match p.array.opaque_owner() {
            Some(p) => Some(alpha_address::<ALLOW_LOADS>(p, bindings, next)?),
            None => None,
        },
        bounds: match p.array.bounds() {
            Some(e) => Some((
                alpha_address::<ALLOW_LOADS>(&e.start, bindings, next)?,
                alpha_machine_key::<ALLOW_LOADS>(V::Shared(&e.width), bindings, next)?,
            )),
            None => None,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        KernelTermExport, MachineBinaryOp, SharedMachineIntegerTerm, SubobjectBounds,
        VerificationSession,
    };
    fn pointer(offset: AddressOffset) -> OldPointer {
        let address = OldAddress {
            base: AddressBase::Concrete("shared-key".into()),
            offset,
        };
        OldPointer::new(address.clone(), ProgramType::VoidPointer)
            .with_provenance(Arc::new(address.clone()))
            .with_bounds(Some(SubobjectBounds {
                start: address,
                width: OldMachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: OldMachineTerm::Variable(Variable(1010002)).into(),
                    right: OldMachineTerm::constant(4).into(),
                },
            }))
            .with_bounds_owner(Some(Arc::new(OldAddress::symbolic(Variable(1010001)))))
    }

    #[test]
    fn shared_keys_match_native_addresses_metadata_and_widths() {
        let _session = VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let scalar =
                SharedMachineIntegerTerm::index(ty, OldMachineTerm::Variable(Variable(1010003)));
            let scaled = if matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32) {
                AddressOffset::int32_scaled(scalar, -4)
            } else {
                AddressOffset::int64_scaled(scalar, 8, true)
            };
            let source = pointer(AddressOffset::raw_add(scaled, AddressOffset::constant(3)));
            let shared = SharedPointer::import(&source);
            let expected = memory_erased_pointer_key(&source);
            let alpha = alpha_program_value_key_with_bindings::<true>(
                &ProgramValue::Pointer(source.clone()),
                &mut fold_keys::bindings(),
                &mut 0,
            );
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(recorded_value(&shared), expected);
            assert_eq!(
                alpha_value::<true>(&shared, &mut fold_keys::bindings(), &mut 0),
                alpha
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
    #[test]
    fn shared_state_selection_retains_checked_match_and_alpha_state_identity() {
        let _session = VerificationSession::enter();
        let address = crate::kernel::SymbolicMemory::global_pointer("shared-key-load");
        let before = crate::kernel::SymbolicMemory::new().with_block("shared-key-load", 16);
        let after = before.clone().store(
            address.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        );
        let make = |memory| {
            SharedPointer::import(&pointer(AddressOffset::int32_scaled(
                SharedMachineIntegerTerm::index(
                    MachineIntegerType::Int32,
                    OldMachineTerm::read_named(
                        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
                        Box::new(address.clone()),
                        LoadKind::Int32,
                    ),
                ),
                4,
            )))
        };
        let a = make(before);
        let b = make(after);
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(recorded_value(&a), recorded_value(&b));
        assert!(recorded_value(&a).requires_checked_match());
        assert_ne!(
            alpha_value::<true>(&a, &mut fold_keys::bindings(), &mut 0),
            alpha_value::<true>(&b, &mut fold_keys::bindings(), &mut 0)
        );
        let mut bindings = fold_keys::bindings();
        bindings.state_aware = false;
        assert!(alpha_value::<false>(&a, &mut bindings, &mut 0).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn shared_address_keys_preserve_load_depth_and_logical_call_identity() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new());
        let mut source = OldAddress::symbolic(Variable(1010200));
        for _ in 0..6 {
            source = OldAddress::loaded_value(&memory, &source);
            let shared = SharedAddress::import(&source);
            assert_eq!(state_address(&shared), memory_erased_address_key(&source));
            assert_eq!(
                alpha_address::<true>(&shared, &mut fold_keys::bindings(), &mut 0),
                alpha_pointer_key_with_bindings::<true>(
                    &source,
                    &mut fold_keys::bindings(),
                    &mut 0
                )
            );
        }
        let make = || {
            SharedAddress::import(&OldAddress {
                base: AddressBase::PureFunctionApplication(
                    crate::kernel::SharedPureApplication::intern("pointer-key-call".into(), vec![]),
                ),
                offset: AddressOffset::constant(0),
            })
        };
        let a = make();
        let b = make();
        assert_ne!(a, b);
        assert_eq!(state_address(&a), state_address(&b));
        assert_eq!(
            alpha_address::<true>(&a, &mut fold_keys::bindings(), &mut 0),
            alpha_address::<true>(&b, &mut fold_keys::bindings(), &mut 0)
        );
    }
    #[test]
    fn compact_key_fingerprints_survive_dropping_all_handles() {
        let fingerprint = || {
            let key = memory_erased_address_offset_key(&AddressOffset::constant(1010301).clone());
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            key.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(fingerprint(), fingerprint());
    }
    #[test]
    fn shared_offset_binders_use_the_selected_scope() {
        let _session = VerificationSession::enter();
        let make = |v| O::Variable(Variable(v)).into_shared().unwrap();
        let a = make(1010101);
        let b = make(1010102);
        let mut left = fold_keys::bindings();
        left.bitvector.insert(Variable(1010101), 0);
        let mut right = fold_keys::bindings();
        right.bitvector.insert(Variable(1010102), 0);
        assert_eq!(
            alpha_offset::<true>(&a, &mut left, &mut 1),
            alpha_offset::<true>(&b, &mut right, &mut 1)
        );
        assert_ne!(
            alpha_offset::<true>(&a, &mut left, &mut 1),
            alpha_offset::<true>(&b, &mut left, &mut 1)
        );
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/pointer_keys.rs");
}
