//! Provenance of C storage created by the executing proof environment.
//!
//! This is only an optional event ledger. It grants no authority or C memory
//! permission, and assumed allocation claims never enter it. A later checked
//! bridge can use an event only while checking a real establishment exchange.

use crate::kernel::PointerBlock;
use crate::persistent::PersistentMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("C population creation identity exhausted")
}

#[derive(Clone)]
struct Root {
    identity: u64,
    invocation: u64,
    pending: PersistentMap<PointerBlock, u64>,
    creators: PersistentMap<PointerBlock, u64>,
}

/// Exact storage-block creation evidence. Copies of a proof path share a root;
/// each transition makes one new root, so state comparison never scans events.
#[derive(Clone)]
pub(in crate::kernel) struct CreationEvents(Arc<Root>);

impl std::fmt::Debug for CreationEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CreationEvents")
            .field("identity", &self.0.identity)
            .field("invocation", &self.0.invocation)
            .field("pending_count", &self.0.pending.len())
            .field("event_count", &self.0.creators.len())
            .finish()
    }
}

impl PartialEq for CreationEvents {
    fn eq(&self, other: &Self) -> bool {
        self.0.identity == other.0.identity
    }
}
impl Eq for CreationEvents {}
impl PartialOrd for CreationEvents {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CreationEvents {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.identity.cmp(&other.0.identity)
    }
}
impl Hash for CreationEvents {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.identity.hash(state);
    }
}

impl CreationEvents {
    pub(in crate::kernel) fn new() -> Self {
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: fresh_identity(),
            pending: PersistentMap::default(),
            creators: PersistentMap::default(),
        }))
    }

    /// A call carries known storage origins but runs in a distinct creator
    /// environment. The caller's current creation rights do not follow it.
    pub(in crate::kernel) fn enter_call(&self) -> Self {
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: fresh_identity(),
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
        }))
    }

    /// Return keeps creation events from the callee but restores the caller's
    /// environment. A callee-created object cannot be established by caller.
    pub(in crate::kernel) fn return_to(&self, caller: &Self) -> Self {
        if self.0.creators.shares_root_with(&caller.0.creators)
            && self.0.pending.shares_root_with(&caller.0.pending)
        {
            return caller.clone();
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: caller.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
        }))
    }

    /// The C `malloc`/`calloc` statement owns an unresolved result. Record
    /// its creator before another function can test the pointer and resolve
    /// the outcome. This is not yet a live-storage creation grant.
    pub(in crate::kernel) fn pending_creation(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(&block, PointerBlock::Symbolic(_)));
        assert!(
            !self.0.pending.contains_key(&block),
            "pending allocation reused"
        );
        let mut pending = self.0.pending.clone();
        pending.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: self.0.invocation,
            pending,
            creators: self.0.creators.clone(),
        }))
    }

    /// Resolve an actual pending allocation. Failure discards its origin;
    /// success attaches the original creator to the trusted Heap block even
    /// when a helper made the deciding branch.
    pub(in crate::kernel) fn resolve_pending(
        &self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
    ) -> Self {
        let Some(creator) = self.0.pending.get(pending_block).copied() else {
            return self.clone();
        };
        let mut pending = self.0.pending.clone();
        pending.remove(pending_block);
        let mut creators = self.0.creators.clone();
        if let Some(block) = live_block {
            debug_assert!(matches!(&block, PointerBlock::Heap(_)));
            assert!(
                !creators.contains_key(&block),
                "storage lifetime created twice"
            );
            creators.insert(block, creator);
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: self.0.invocation,
            pending,
            creators,
        }))
    }

    /// Called only at checked C storage creation, never at resource lowering,
    /// contract allocation import, or generic memory-block construction.
    #[cfg(test)]
    pub(in crate::kernel) fn created(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(block, PointerBlock::Heap(_)) || block.starts_with("local:"));
        let mut creators = self.0.creators.clone();
        assert!(
            !creators.contains_key(&block),
            "storage lifetime created twice"
        );
        creators.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
        }))
    }

    pub(in crate::kernel) fn created_here(&self, block: &PointerBlock) -> bool {
        self.0.creators.get(block).copied() == Some(self.0.invocation)
    }

    /// End of an automatic or heap lifetime removes its provenance. Future
    /// reuse at the same address needs an independently checked creation.
    pub(in crate::kernel) fn retired(&self, block: &PointerBlock) -> Self {
        if !self.0.creators.contains_key(block) {
            return self.clone();
        }
        let mut creators = self.0.creators.clone();
        creators.remove(block);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
        }))
    }
}

#[cfg(test)]
mod tests;
