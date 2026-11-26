//! Complete pointer identity without exporting the enclosing descriptor.
//! Offset indices keep exactly the handles used by native OldAddressOffset.
use super::*;
use crate::kernel::{KernelAddressOffset, SharedAddress, SharedAddressOffset};
use crate::kernel::{OffsetTree, OffsetView};

#[derive(Clone, Debug)]
pub(in crate::kernel) struct PointerStorageKey(Arc<PointerData>);
#[derive(Debug)]
struct PointerData {
    identity: PointerIdentity,
    fingerprint: u64,
}
// Field order is Pointer::identity, not address equality or producer identity.
#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct PointerIdentity {
    address: AddressKey,
    provenance: AddressKey,
    bounds_known: bool,
    bounds_owner: Option<AddressKey>,
    bounds: Option<(AddressKey, ScalarStorageKey)>,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) struct AddressKey {
    block: AddressBase,
    offset: OffsetKey,
}
impl AddressKey {
    pub(in crate::kernel) fn native(pointer: &OldAddress) -> Self {
        Self {
            block: pointer.base.clone(),
            offset: OffsetKey::native(&pointer.offset),
        }
    }
    pub(in crate::kernel) fn shared(pointer: &SharedAddress) -> Self {
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
    pub(in crate::kernel) fn native(value: &OldPointer) -> Self {
        Self::new(PointerIdentity {
            address: AddressKey::native(value.address()),
            provenance: AddressKey::native(value.provenance()),
            bounds_known: value.bounds_are_known(),
            bounds_owner: (!value.bounds_are_known())
                .then(|| value.bounds_owner().map(AddressKey::native))
                .flatten(),
            bounds: value.bounds().map(|e| {
                (
                    AddressKey::native(&e.start),
                    ScalarStorageKey::native(&e.width),
                )
            }),
        })
    }
    pub(super) fn shared(value: &SharedPointer) -> Self {
        let value = value.node();
        Self::new(PointerIdentity {
            address: AddressKey::shared(&value.address),
            provenance: AddressKey::shared(&value.provenance),
            bounds_known: value.array.is_known(),
            bounds_owner: value.array.opaque_owner().map(AddressKey::shared),
            bounds: value
                .array
                .bounds()
                .map(|e| (AddressKey::shared(&e.start), e.width.scalar_storage_key())),
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
pub(in crate::kernel) struct OffsetKey(OffsetShape);
#[derive(Clone, Debug)]
enum OffsetShape {
    // The native leaf is already the exact offset identity. Keep these
    // inline, especially constant offsets in ordinary resource keys.
    Leaf(OldAddressOffset),
    Add(Arc<OffsetAdd>),
}
#[derive(Debug)]
struct OffsetAdd {
    children: [OffsetKey; 2],
    fingerprint: u64,
}

impl OffsetKey {
    fn add(children: [Self; 2]) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        children.hash(&mut hash);
        Self(OffsetShape::Add(Arc::new(OffsetAdd {
            children,
            fingerprint: hash.finish(),
        })))
    }

    fn rank(&self) -> u8 {
        match &self.0 {
            OffsetShape::Add(_) => 2,
            OffsetShape::Leaf(leaf) => match leaf.view() {
                OffsetView::Constant(_) => 0,
                OffsetView::Variable(_) => 1,
                OffsetView::Int32Scaled { .. } => 3,
                OffsetView::Int64Scaled { .. } => 4,
                OffsetView::Add(..) => unreachable!("offset leaf"),
            },
        }
    }

    pub(in crate::kernel) fn native(source: &OldAddressOffset) -> Self {
        if !matches!(source.view(), OffsetView::Add(..)) {
            return Self(OffsetShape::Leaf(source.clone()));
        }
        enum Task<'a> {
            Enter(&'a OldAddressOffset),
            Add,
        }
        let mut pending = vec![Task::Enter(source)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(offset) => match offset.view() {
                    OffsetView::Add(a, b) => {
                        pending.extend([Task::Add, Task::Enter(b), Task::Enter(a)]);
                    }
                    _ => values.push(Self(OffsetShape::Leaf(offset.clone()))),
                },
                Task::Add => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::add([a, b]));
                }
            }
        }
        values.pop().expect("offset key")
    }

    pub(in crate::kernel) fn matches_root(&self, source: &SharedAddressOffset) -> bool {
        self.rank()
            == match source.node() {
                KernelAddressOffset::Constant(_) => 0,
                KernelAddressOffset::Variable(_) => 1,
                KernelAddressOffset::Add(_) => 2,
                KernelAddressOffset::Int32Scaled { .. } => 3,
                KernelAddressOffset::Int64Scaled { .. } => 4,
            }
            && *self == offset_for_root(source)
    }

    fn shared(source: &SharedAddressOffset) -> Self {
        let index = |root: &KernelTerm| {
            KernelAddressOffset::index_key(root).expect("selected offset index key")
        };
        Self(OffsetShape::Leaf(match source.node() {
            KernelAddressOffset::Constant(v) => OldAddressOffset::constant(*v),
            KernelAddressOffset::Variable(v) => OldAddressOffset::variable(*v),
            KernelAddressOffset::Add(children) => {
                return Self::add(children.each_ref().map(offset_for_root));
            }
            KernelAddressOffset::Int32Scaled { value, byte_width } => {
                OldAddressOffset::int32_scaled(index(value), *byte_width)
            }
            KernelAddressOffset::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => OldAddressOffset::int64_scaled(index(value), *byte_width, *unsigned),
        }))
    }
}
impl Hash for OffsetKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            OffsetShape::Leaf(leaf) => leaf.hash(state),
            OffsetShape::Add(add) => {
                2usize.hash(state);
                add.fingerprint.hash(state);
            }
        }
    }
}
impl PartialEq for OffsetKey {
    fn eq(&self, other: &Self) -> bool {
        if let (OffsetShape::Add(a), OffsetShape::Add(b)) = (&self.0, &other.0)
            && a.fingerprint != b.fingerprint
        {
            return false;
        }
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
        match (&self.0, &other.0) {
            (OffsetShape::Leaf(a), OffsetShape::Leaf(b)) => return a.cmp(b),
            (OffsetShape::Add(_), OffsetShape::Add(_)) => {}
            _ => return self.rank().cmp(&other.rank()),
        }
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            let order = match (&a.0, &b.0) {
                (OffsetShape::Leaf(a), OffsetShape::Leaf(b)) => a.cmp(b),
                (OffsetShape::Add(a), OffsetShape::Add(b)) => {
                    if !Arc::ptr_eq(a, b) && seen.insert((Arc::as_ptr(a), Arc::as_ptr(b))) {
                        crate::instrumentation::record_deterministic_work(1);
                        pending.extend(a.children.iter().zip(&b.children).rev());
                    }
                    Ordering::Equal
                }
                _ => a.rank().cmp(&b.rank()),
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
            if let OffsetShape::Add(add) = &mut key.0
                && let Some(add) = Arc::get_mut(add)
            {
                let leaf = || OffsetKey(OffsetShape::Leaf(OldAddressOffset::constant(0)));
                pending.extend(std::mem::replace(&mut add.children, [leaf(), leaf()]));
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
pub(in crate::kernel) fn offset_for_root(source: &SharedAddressOffset) -> OffsetKey {
    if !matches!(source.node(), KernelAddressOffset::Add(_)) {
        return OffsetKey::shared(source);
    }
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
