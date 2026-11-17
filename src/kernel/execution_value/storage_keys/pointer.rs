//! Complete pointer identity without exporting the enclosing descriptor.
//! Offset indices keep exactly the handles used by native AddressOffset.
use super::*;
use crate::kernel::{KernelAddressOffset, SharedAddress, SharedAddressOffset};

#[derive(Clone, Debug)]
pub(in crate::kernel) struct PointerStorageKey(Arc<PointerData>);
#[derive(Debug)]
struct PointerData {
    identity: PointerIdentity,
    fingerprint: u64,
}
// Field order is PointerValue::identity, not address equality or producer identity.
#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct PointerIdentity {
    address: AddressKey,
    provenance: AddressKey,
    program_type: ProgramType,
    volatile: bool,
    bounds_known: bool,
    bounds_owner: Option<AddressKey>,
    bounds: Option<(AddressKey, MachineTerm)>,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct AddressKey {
    block: AddressBase,
    offset: OffsetKey,
}
impl AddressKey {
    fn native(pointer: &Address) -> Self {
        Self {
            block: pointer.base.clone(),
            offset: OffsetKey::native(&pointer.offset),
        }
    }
    fn shared(pointer: &SharedAddress) -> Self {
        Self {
            block: pointer.node().base.native_atom().clone(),
            offset: offset_for_root(&pointer.node().offset),
        }
    }
}
impl PointerStorageKey {
    fn new(identity: PointerIdentity) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        identity.hash(&mut hash);
        Self(Arc::new(PointerData {
            identity,
            fingerprint: hash.finish(),
        }))
    }
    pub(in crate::kernel) fn native(value: &PointerValue) -> Self {
        Self::new(PointerIdentity {
            address: AddressKey::native(value.pointer()),
            provenance: AddressKey::native(value.provenance()),
            program_type: value.program_type(),
            volatile: value.pointee_volatile(),
            bounds_known: value.bounds_are_known(),
            bounds_owner: (!value.bounds_are_known())
                .then(|| value.bounds_owner().map(AddressKey::native))
                .flatten(),
            bounds: value
                .bounds()
                .map(|e| (AddressKey::native(&e.start), e.width.clone())),
        })
    }
    fn shared(value: &SharedPointerValue) -> Self {
        let value = value.node();
        let q = value.qualifiers.as_deref();
        let bounds_known = q.is_some_and(|q| q.bounds_known);
        Self::new(PointerIdentity {
            address: AddressKey::shared(&value.address),
            provenance: AddressKey::shared(&value.provenance),
            program_type: value.program_type,
            volatile: q.is_some_and(|q| q.volatile),
            bounds_known,
            bounds_owner: (!bounds_known)
                .then(|| value.bounds_owner.as_ref().map(AddressKey::shared))
                .flatten(),
            // Widths have native MachineTerm structural identity, unlike offset
            // index handles. Keep this selected scalar adapter explicit.
            bounds: q.and_then(|q| q.bounds.as_ref()).map(|e| {
                (
                    AddressKey::shared(&e.start),
                    KernelTermExport::machine(&e.width).expect("selected subobject width"),
                )
            }),
        })
    }
}
impl Hash for PointerStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state)
    }
}
impl PartialEq for PointerStorageKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.identity == other.0.identity
    }
}
impl Eq for PointerStorageKey {}
impl PartialOrd for PointerStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PointerStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            Ordering::Equal
        } else {
            self.0.identity.cmp(&other.0.identity)
        }
    }
}

#[derive(Clone, Debug)]
struct OffsetKey(Arc<OffsetData>);
#[derive(Debug)]
struct OffsetData {
    shape: OffsetShape,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum OffsetShape {
    Constant(i64),
    Variable(Variable),
    Add([OffsetKey; 2]),
    Int32Scaled(SharedMachineIntegerTerm, i64),
    Int64Scaled(SharedMachineIntegerTerm, i64, bool),
}
impl OffsetShape {
    fn rank(&self) -> u8 {
        match self {
            Self::Constant(_) => 0,
            Self::Variable(_) => 1,
            Self::Add(_) => 2,
            Self::Int32Scaled(..) => 3,
            Self::Int64Scaled(..) => 4,
        }
    }
}
impl OffsetKey {
    fn new(shape: OffsetShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(OffsetData {
            shape,
            fingerprint: hash.finish(),
        }))
    }
    fn native(source: &AddressOffset) -> Self {
        enum Task<'a> {
            Enter(&'a AddressOffset),
            Add,
        }
        let mut pending = vec![Task::Enter(source)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            let shape = match task {
                Task::Enter(AddressOffset::Constant(v)) => OffsetShape::Constant(*v),
                Task::Enter(AddressOffset::Variable(v)) => OffsetShape::Variable(*v),
                Task::Enter(AddressOffset::Add(a, b)) => {
                    pending.extend([Task::Add, Task::Enter(b), Task::Enter(a)]);
                    continue;
                }
                Task::Enter(AddressOffset::Int32Scaled { value, byte_width }) => {
                    OffsetShape::Int32Scaled(value.clone(), *byte_width)
                }
                Task::Enter(AddressOffset::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                }) => OffsetShape::Int64Scaled(value.clone(), *byte_width, *unsigned),
                Task::Add => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    OffsetShape::Add([a, b])
                }
            };
            values.push(Self::new(shape));
        }
        values.pop().expect("offset key")
    }
    fn shared(source: &SharedAddressOffset) -> Self {
        let index = |root: &KernelTerm| {
            KernelAddressOffset::index_key(root).expect("selected offset index key")
        };
        Self::new(match source.node() {
            KernelAddressOffset::Constant(v) => OffsetShape::Constant(*v),
            KernelAddressOffset::Variable(v) => OffsetShape::Variable(*v),
            KernelAddressOffset::Add(children) => {
                OffsetShape::Add(children.each_ref().map(offset_for_root))
            }
            KernelAddressOffset::Int32Scaled { value, byte_width } => {
                OffsetShape::Int32Scaled(index(value), *byte_width)
            }
            KernelAddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => OffsetShape::Int64Scaled(index(value), *byte_width, *unsigned),
        })
    }
}
impl Hash for OffsetKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state)
    }
}
impl PartialEq for OffsetKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for OffsetKey {}
impl PartialOrd for OffsetKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for OffsetKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            if Arc::ptr_eq(&a.0, &b.0) || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let order = a.0.shape.rank().cmp(&b.0.shape.rank());
            if !order.is_eq() {
                return order;
            }
            let order = match (&a.0.shape, &b.0.shape) {
                (OffsetShape::Constant(a), OffsetShape::Constant(b)) => a.cmp(b),
                (OffsetShape::Variable(a), OffsetShape::Variable(b)) => a.cmp(b),
                (OffsetShape::Add(a), OffsetShape::Add(b)) => {
                    pending.extend(a.iter().zip(b).rev());
                    Ordering::Equal
                }
                (OffsetShape::Int32Scaled(a, aw), OffsetShape::Int32Scaled(b, bw)) => {
                    (a, aw).cmp(&(b, bw))
                }
                (OffsetShape::Int64Scaled(a, aw, au), OffsetShape::Int64Scaled(b, bw, bu)) => {
                    (a, aw, au).cmp(&(b, bw, bu))
                }
                _ => unreachable!("same offset variant"),
            };
            if !order.is_eq() {
                return order;
            }
        }
        Ordering::Equal
    }
}
impl Drop for OffsetKey {
    fn drop(&mut self) {
        fn take(key: &mut OffsetKey, pending: &mut Vec<OffsetKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0) {
                if let OffsetShape::Add(children) =
                    std::mem::replace(&mut data.shape, OffsetShape::Constant(0))
                {
                    pending.extend(children);
                }
            }
        }
        let mut pending = Vec::new();
        take(self, &mut pending);
        while let Some(mut key) = pending.pop() {
            take(&mut key, &mut pending);
        }
    }
}
thread_local! {
    static OFFSETS: std::cell::RefCell<std::collections::HashMap<SharedAddressOffset, OffsetKey>> = Default::default();
    static POINTERS: std::cell::RefCell<crate::id_hash::U64Map<PointerStorageKey>> = Default::default();
}
fn offset_for_root(source: &SharedAddressOffset) -> OffsetKey {
    OFFSETS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(root) {
                continue;
            }
            if !finish && let KernelAddressOffset::Add(children) = root.node() {
                pending.push((root, true));
                pending.extend(children.iter().rev().map(|child| (child, false)));
                continue;
            }
            let key = OffsetKey::shared(root);
            keys.borrow_mut().insert(root.clone(), key);
        }
        keys.borrow()
            .get(source)
            .expect("shared offset key")
            .clone()
    })
}
pub(in crate::kernel) fn for_root(source: &KernelTerm) -> PointerStorageKey {
    POINTERS.with(|keys| {
        if let Some(key) = keys.borrow().get(&source.id()) {
            return key.clone();
        }
        let key =
            PointerStorageKey::shared(source.pointer_payload().expect("retained pointer key"));
        keys.borrow_mut().insert(source.id(), key.clone());
        key
    })
}
pub(super) fn clear_session_key_memos() {
    POINTERS.with(|keys| keys.borrow_mut().clear());
    OFFSETS.with(|keys| keys.borrow_mut().clear());
}
