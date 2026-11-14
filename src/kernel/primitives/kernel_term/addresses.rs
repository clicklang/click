//! Raw addresses retain block identity and shared displacement. Exact producer
//! identity is distinct from the logical pointer equality used by checking.
use super::offsets::{KernelPointerOffset, SharedPointerOffset};
use super::*;

#[derive(Clone, Debug)]
struct ExactBlock {
    source: Arc<PointerBlock>,
    fingerprint: u64,
}
impl ExactBlock {
    fn new(block: &PointerBlock) -> Self {
        let bytes = match block {
            PointerBlock::Concrete(name) | PointerBlock::Function(name) => name.len(),
            PointerBlock::StringLiteral { identity, bytes } => {
                identity.len().saturating_add(bytes.len())
            }
            _ => 0,
        };
        crate::instrumentation::record_deterministic_work(bytes);
        let mut hash = crate::id_hash::FingerprintHasher::default();
        match block {
            PointerBlock::PureFunctionApplication(call) => {
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
            (
                PointerBlock::PureFunctionApplication(a),
                PointerBlock::PureFunctionApplication(b),
            ) => a.payload_id() == b.payload_id(),
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
pub(crate) struct SharedPointerBlock(Arc<BlockData>);
struct BlockData {
    id: u64,
    source: ExactBlock,
}
impl std::fmt::Debug for SharedPointerBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedPointerBlock")
            .field(&self.0.id)
            .finish()
    }
}
impl PartialEq for SharedPointerBlock {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for SharedPointerBlock {}
impl Hash for SharedPointerBlock {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}
#[derive(Default)]
struct BlockInterner {
    nodes: HashMap<ExactBlock, Weak<BlockData>>,
    cleanup: VecDeque<ExactBlock>,
    next_id: u64,
}
impl SharedPointerBlock {
    pub(crate) fn import(block: &PointerBlock) -> Self {
        // Import reads this selected atom once. Call payloads remain explicit
        // compatibility handles until the pointer-call producer slice.
        crate::instrumentation::record_deterministic_work(9);
        static INTERNER: std::sync::OnceLock<Mutex<BlockInterner>> = std::sync::OnceLock::new();
        let mut arena = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("block arena");
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
        let key = ExactBlock::new(block);
        if let Some(node) = arena.nodes.get(&key).and_then(Weak::upgrade) {
            return Self(node);
        }
        let id = arena.next_id;
        arena.next_id = id.checked_add(1).expect("block identity exhausted");
        let node = Arc::new(BlockData {
            id,
            source: key.clone(),
        });
        arena.nodes.insert(key.clone(), Arc::downgrade(&node));
        arena.cleanup.push_back(key);
        Self(node)
    }
    pub(crate) fn native_atom(&self) -> &PointerBlock {
        &self.0.source.source
    }
}

/// Cloning, comparing and hashing prepared addresses inspect only handles.
/// There is no retained native Pointer or native offset tree.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct SharedPointerAddress(Arc<KernelPointerAddress>);
#[derive(Debug, Eq, PartialEq, Hash)]
pub(crate) struct KernelPointerAddress {
    pub(crate) block: SharedPointerBlock,
    pub(crate) offset: SharedPointerOffset,
}
impl SharedPointerAddress {
    pub(crate) fn new(block: SharedPointerBlock, offset: SharedPointerOffset) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        Self(Arc::new(KernelPointerAddress { block, offset }))
    }
    pub(crate) fn node(&self) -> &KernelPointerAddress {
        &self.0
    }
    pub(crate) fn import(pointer: &Pointer) -> Self {
        Self::new(
            SharedPointerBlock::import(&pointer.block),
            KernelPointerOffset::import(&pointer.offset),
        )
    }
    pub(crate) fn export(&self) -> Result<Pointer, &'static str> {
        Ok(Pointer {
            block: self.0.block.native_atom().clone(),
            offset: KernelPointerOffset::export(&self.0.offset)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn address_atoms_round_trip_without_changing_identity_or_offset_shape() {
        let blocks = vec![
            PointerBlock::Concrete("object".into()),
            PointerBlock::StringLiteral {
                identity: "literal".into(),
                bytes: vec![0, 255],
            },
            PointerBlock::Function("function".into()),
            PointerBlock::FunctionSymbolic(Variable(998001)),
            PointerBlock::ExternalArgument,
            PointerBlock::ExternalObject(Variable(998002)),
            PointerBlock::Symbolic(Variable(998003)),
            PointerBlock::LoadedPointer(PointerLoadId(998004)),
            PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
                "call".into(),
                vec![],
            )),
            PointerBlock::Heap(998005),
            PointerBlock::Temporary(998006),
        ];
        for block in blocks {
            let source = Pointer {
                block,
                offset: PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Constant(0)),
                    Box::new(PointerOffsetTerm::Variable(Variable(998007))),
                ),
            };
            let shared = SharedPointerAddress::import(&source);
            assert_eq!(shared.export().unwrap(), source);
            assert_eq!(SharedPointerAddress::import(&source), shared);
            assert!(matches!(
                shared.node().offset.node(),
                KernelPointerOffset::Add(_)
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
            SharedPointerAddress::import(&Pointer {
                block: PointerBlock::PureFunctionApplication(call),
                offset: PointerOffsetTerm::Constant(0),
            })
        };
        let left = address(a.clone());
        let right = address(b);
        assert_ne!(left, right);
        assert_eq!(left.export().unwrap(), right.export().unwrap());
        let PointerBlock::PureFunctionApplication(output) = left.export().unwrap().block else {
            panic!("call")
        };
        assert_eq!(output.payload_id(), a.payload_id());
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/addresses.rs");
}
