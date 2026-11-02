//! Session-interned conjunction nodes. Index keys contain only the two direct
//! operands; an operand conjunction is compared and hashed by its node id.
use super::CResource;
use std::{
    cell::RefCell,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

#[derive(Debug)]
pub struct ResourceConjunction {
    id: u64,
    children: (CResource, CResource),
}
impl std::ops::Deref for ResourceConjunction {
    type Target = (CResource, CResource);
    fn deref(&self) -> &Self::Target {
        &self.children
    }
}
impl PartialEq for ResourceConjunction {
    fn eq(&self, other: &Self) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.id == other.id
    }
}
impl Eq for ResourceConjunction {}
impl PartialOrd for ResourceConjunction {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ResourceConjunction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}
impl std::hash::Hash for ResourceConjunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        crate::instrumentation::record_deterministic_work(1);
        self.id.hash(state);
    }
}

pub(super) type Registry =
    crate::persistent::PersistentMap<(CResource, CResource), Arc<ResourceConjunction>>;
thread_local! { static NODES: RefCell<Registry> = RefCell::new(Registry::default()); }
static NEXT: AtomicU64 = AtomicU64::new(1);
pub(super) fn intern(left: CResource, right: CResource) -> Arc<ResourceConjunction> {
    crate::instrumentation::record_deterministic_work(1);
    NODES.with(|nodes| {
        let mut nodes = nodes.borrow_mut();
        let key = (left, right);
        if let Some(node) = nodes.get(&key) {
            return node.clone();
        }
        let node = Arc::new(ResourceConjunction {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            children: key.clone(),
        });
        nodes.insert(key, node.clone());
        node
    })
}
pub(super) fn capture() -> Registry {
    NODES.with(|nodes| nodes.borrow().clone())
}
pub(super) fn restore(state: &Registry) {
    NODES.with(|nodes| *nodes.borrow_mut() = state.clone());
}
pub(super) fn clear() {
    NODES.with(|nodes| *nodes.borrow_mut() = Registry::default());
}

#[cfg(test)]
pub(super) fn len() -> usize {
    NODES.with(|nodes| nodes.borrow().len())
}
