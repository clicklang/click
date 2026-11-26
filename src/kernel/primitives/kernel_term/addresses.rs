//! Raw addresses retain block identity and shared displacement. Exact producer
//! identity is distinct from the logical pointer equality used by checking.
use super::offsets::{KernelAddressOffset, SharedAddressOffset};
use super::*;

#[derive(Clone, Debug)]
struct ExactBlock {
    source: Arc<AddressBase>,
    fingerprint: u64,
}
impl ExactBlock {
    fn new(block: &AddressBase) -> Self {
        let bytes = match block {
            AddressBase::Concrete(name) | AddressBase::Function(name) => name.len(),
            AddressBase::StringLiteral { identity, bytes } => {
                identity.payload_bytes().saturating_add(bytes.len())
            }
            _ => 0,
        };
        crate::instrumentation::record_deterministic_work(bytes);
        let mut hash = crate::id_hash::FingerprintHasher::default();
        match block {
            AddressBase::PureFunctionApplication(call) => {
                10u64.hash(&mut hash);
                call.payload_id().hash(&mut hash);
            }
            block => block.hash(&mut hash),
        }
        Self {
            source: Arc::new(block.clone()),
            fingerprint: hash.finish(),
        }
    }
}
impl PartialEq for ExactBlock {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.source, &other.source) {
            return true;
        }
        match (&*self.source, &*other.source) {
            (AddressBase::PureFunctionApplication(a), AddressBase::PureFunctionApplication(b)) => {
                a.payload_id() == b.payload_id()
            }
            (a, b) => a == b,
        }
    }
}
impl Eq for ExactBlock {}
impl Hash for ExactBlock {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fingerprint.hash(state);
    }
}

#[derive(Clone)]
pub(crate) struct SharedAddressBase(BlockStorage);
#[derive(Clone)]
enum BlockStorage {
    // These atoms already have scalar identities. They need neither an arena
    // allocation nor weak-entry cleanup on every read descriptor import.
    Inline(AddressBase),
    Interned(Arc<BlockData>),
}
struct BlockData {
    id: u64,
    source: ExactBlock,
}
impl std::fmt::Debug for SharedAddressBase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            BlockStorage::Inline(block) => f.debug_tuple("SharedAddressBase").field(block).finish(),
            BlockStorage::Interned(node) => {
                f.debug_tuple("SharedAddressBase").field(&node.id).finish()
            }
        }
    }
}
impl PartialEq for SharedAddressBase {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (BlockStorage::Inline(a), BlockStorage::Inline(b)) => a == b,
            (BlockStorage::Interned(a), BlockStorage::Interned(b)) => a.id == b.id,
            _ => false,
        }
    }
}
impl Eq for SharedAddressBase {}
impl Hash for SharedAddressBase {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            BlockStorage::Inline(block) => {
                0u8.hash(state);
                block.hash(state);
            }
            BlockStorage::Interned(node) => {
                1u8.hash(state);
                node.id.hash(state);
            }
        }
    }
}
#[derive(Default)]
struct BlockInterner {
    nodes: HashMap<ExactBlock, Weak<BlockData>>,
    cleanup: VecDeque<ExactBlock>,
    next_id: u64,
}
impl SharedAddressBase {
    pub(crate) fn import(block: &AddressBase) -> Self {
        Self::import_with_upkeep(block, false)
    }

    fn import_with_upkeep(block: &AddressBase, producer: bool) -> Self {
        if matches!(
            block,
            AddressBase::Symbolic(_)
                | AddressBase::FunctionSymbolic(_)
                | AddressBase::ExternalArgument
                | AddressBase::ExternalObject(_)
                | AddressBase::Load(_)
                | AddressBase::Heap(_)
                | AddressBase::Temporary(_)
        ) {
            crate::instrumentation::record_deterministic_work(1);
            return Self(BlockStorage::Inline(block.clone()));
        }
        // Import reads this selected atom once. Call payloads remain explicit
        // compatibility handles until the pointer-call producer slice.
        crate::instrumentation::record_deterministic_work(1);
        static INTERNER: std::sync::OnceLock<Mutex<BlockInterner>> = std::sync::OnceLock::new();
        let mut arena = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("block arena");
        let key = ExactBlock::new(block);
        let live = arena.nodes.get(&key).and_then(Weak::upgrade);
        // A new pointer producer advances bounded arena upkeep, even when its
        // named block is already live. Later descriptor imports reuse live
        // components without upkeep. Admission therefore has the same work
        // whether another verification previously used this block spelling.
        if producer || live.is_none() {
            crate::instrumentation::record_deterministic_work(8);
            for _ in 0..arena.cleanup.len().min(8) {
                let key = arena.cleanup.pop_front().unwrap();
                if arena
                    .nodes
                    .get(&key)
                    .is_some_and(|node| node.strong_count() == 0)
                {
                    arena.nodes.remove(&key);
                } else {
                    arena.cleanup.push_back(key);
                }
            }
        }
        if let Some(node) = live {
            return Self(BlockStorage::Interned(node));
        }
        let id = arena.next_id;
        arena.next_id = id.checked_add(1).expect("block identity exhausted");
        let node = Arc::new(BlockData {
            id,
            source: key.clone(),
        });
        arena.nodes.insert(key.clone(), Arc::downgrade(&node));
        arena.cleanup.push_back(key);
        Self(BlockStorage::Interned(node))
    }
    /// Observation keys use the application's semantic scalar identity.
    /// Producer imports continue to retain its exact payload identity.
    pub(crate) fn observation(&self) -> Self {
        match self.native_atom() {
            block @ AddressBase::PureFunctionApplication(_) => {
                Self(BlockStorage::Inline(block.clone()))
            }
            _ => self.clone(),
        }
    }

    pub(crate) fn native_atom(&self) -> &AddressBase {
        match &self.0 {
            BlockStorage::Inline(block) => block,
            BlockStorage::Interned(node) => &node.source.source,
        }
    }
}

/// Cloning, comparing and hashing prepared addresses inspect only handles.
/// Exact native cell lookups borrow a lazily prepared address.
#[derive(Clone)]
pub struct SharedAddress(Arc<SharedAddressData>);

struct SharedAddressData {
    node: KernelAddress,
    cell_key: std::sync::OnceLock<OldAddress>,
}

impl std::fmt::Debug for SharedAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedAddress").field(self.node()).finish()
    }
}

impl PartialEq for SharedAddress {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.node() == other.node()
    }
}

impl Eq for SharedAddress {}

impl Hash for SharedAddress {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node().hash(state);
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub(crate) struct KernelAddress {
    pub(crate) base: SharedAddressBase,
    pub(crate) offset: SharedAddressOffset,
}
impl SharedAddress {
    pub(crate) fn new(base: SharedAddressBase, offset: SharedAddressOffset) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(Arc::new(SharedAddressData {
            node: KernelAddress { base, offset },
            cell_key: std::sync::OnceLock::new(),
        }))
    }
    pub(crate) fn node(&self) -> &KernelAddress {
        &self.0.node
    }
    pub(crate) fn import(pointer: &OldAddress) -> Self {
        Self::new(
            SharedAddressBase::import(&pointer.base),
            KernelAddressOffset::import(&pointer.offset),
        )
    }
    pub(crate) fn import_produced(pointer: &OldAddress) -> Self {
        Self::new(
            SharedAddressBase::import_with_upkeep(&pointer.base, true),
            KernelAddressOffset::import(&pointer.offset),
        )
    }
    pub(crate) fn syntax_equal(&self, other: &Self) -> bool {
        (self.node().base == other.node().base
            || self.node().base.native_atom() == other.node().base.native_atom())
            && self.node().offset.syntax_equal(&other.node().offset)
    }

    pub(crate) fn export(&self) -> Result<OldAddress, &'static str> {
        Ok(OldAddress {
            base: self.node().base.native_atom().clone(),
            offset: KernelAddressOffset::export(&self.node().offset)?,
        })
    }

    pub(crate) fn exact_cell_key(&self) -> &OldAddress {
        self.0
            .cell_key
            .get_or_init(|| self.export().expect("retained read address"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn address_atoms_round_trip_without_changing_identity_or_offset_shape() {
        let blocks = vec![
            AddressBase::Concrete("object".into()),
            AddressBase::StringLiteral {
                identity: StringLiteralId::new("literal", 0),
                bytes: vec![0, 255],
            },
            AddressBase::Function("function".into()),
            AddressBase::FunctionSymbolic(Variable(998001)),
            AddressBase::ExternalArgument,
            AddressBase::ExternalObject(Variable(998002)),
            AddressBase::Symbolic(Variable(998003)),
            OldAddress::loaded_value(
                &crate::kernel::intern_memory(SymbolicMemory::new()),
                &OldAddress::symbolic(Variable(998004)),
            )
            .base,
            AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "call".into(),
                vec![],
            )),
            AddressBase::Heap(998005),
            AddressBase::Temporary(998006),
        ];
        for block in blocks {
            let source = OldAddress {
                base: block,
                offset: OldAddressOffset::Add(
                    Box::new(OldAddressOffset::Constant(0)),
                    Box::new(OldAddressOffset::Variable(Variable(998007))),
                ),
            };
            let shared = SharedAddress::import(&source);
            assert_eq!(shared.export().unwrap(), source);
            assert_eq!(SharedAddress::import(&source), shared);
            assert!(matches!(
                shared.node().offset.node(),
                KernelAddressOffset::Add(_)
            ));
        }
    }
    #[test]
    fn exact_call_payloads_remain_separate_from_logical_call_identity() {
        let a = SharedPureApplication::intern("call".into(), vec![]);
        let b = SharedPureApplication::intern("call".into(), vec![]);
        assert_eq!(a, b);
        assert_ne!(a.payload_id(), b.payload_id());
        let address = |call| {
            SharedAddress::import(&OldAddress {
                base: AddressBase::PureFunctionApplication(call),
                offset: OldAddressOffset::Constant(0),
            })
        };
        let left = address(a.clone());
        let right = address(b);
        assert_ne!(left, right);
        assert_eq!(left.export().unwrap(), right.export().unwrap());
        let AddressBase::PureFunctionApplication(output) = left.export().unwrap().base else {
            panic!("call")
        };
        assert_eq!(output.payload_id(), a.payload_id());
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/addresses.rs");
}
