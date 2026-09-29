//! Provenance of C storage created by the executing proof environment.
//!
//! This optional event ledger binds abstract population authority to checked
//! C storage creation. It grants no C memory permission, and assumed
//! allocation claims never enter it.

use super::{Anchor, AuthorityState, Holder, Refusal};
use crate::kernel::{PointerBlock, ResourceDescription};
use crate::persistent::{PersistentMap, PersistentSet};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("C population creation identity exhausted")
}

#[derive(Clone)]
struct Root {
    identity: u64,
    /// Stable rechecking of the same function-entry transition. Authority-mode C
    /// calls remain closed until each occurrence has its own identity.
    entry_call: OnceLock<CreationEvents>,
    invocation: Holder,
    pending: PersistentMap<PointerBlock, Holder>,
    creators: PersistentMap<PointerBlock, Holder>,
    anchors: PersistentMap<PointerBlock, Anchor>,
    authority: AuthorityState,
    /// Per-storage family history; never inferred from the current owner.
    tainted: PersistentMap<PointerBlock, PersistentSet<String>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum CreationRefusal {
    NotCreationEnvironment,
    MembersAlreadyExisted,
    AlreadyEstablished,
    MissingAuthority,
    OutstandingMembers,
    OutstandingAuthority,
}

impl From<Refusal> for CreationRefusal {
    fn from(value: Refusal) -> Self {
        match value {
            Refusal::AlreadyEstablished => Self::AlreadyEstablished,
            Refusal::OutstandingMembers => Self::OutstandingMembers,
            Refusal::OutstandingAuthority => Self::OutstandingAuthority,
            Refusal::MissingAuthority | Refusal::UnknownPopulation => Self::MissingAuthority,
            _ => Self::NotCreationEnvironment,
        }
    }
}

/// Opaque evidence issued only by a checked transition that minted the
/// resulting abstract population identity. Certificate checking compares exact state roots;
/// it never tries to allocate the same identity a second time.
#[derive(Clone, Debug)]
pub(crate) struct CheckedPopulationAuthorityExchange {
    before: u64,
    after: u64,
    description: ResourceDescription,
    establish: bool,
}

impl CheckedPopulationAuthorityExchange {
    pub(in crate::kernel) fn matches(
        &self,
        before: &CreationEvents,
        after: &CreationEvents,
        description: &ResourceDescription,
        establish: bool,
    ) -> bool {
        self.before == before.0.identity
            && self.after == after.0.identity
            && &self.description == description
            && self.establish == establish
    }
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
            .field("anchor_count", &self.0.anchors.len())
            .field("tainted_blocks", &self.0.tainted.len())
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
            entry_call: OnceLock::new(),
            invocation: Holder::fresh(),
            pending: PersistentMap::default(),
            creators: PersistentMap::default(),
            anchors: PersistentMap::default(),
            authority: AuthorityState::default(),
            tainted: PersistentMap::default(),
        }))
    }

    /// A call carries known storage origins but runs in a distinct creator
    /// environment. The caller's current creation rights do not follow it.
    /// Rechecking one entry must recover exactly the same child identity.
    /// Distinct C call occurrences need their own event key before calls are
    /// enabled in authority mode.
    pub(in crate::kernel) fn enter_call(&self) -> Self {
        self.0
            .entry_call
            .get_or_init(|| {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    invocation: Holder::fresh(),
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority: self.0.authority.clone(),
                    tainted: self.0.tainted.clone(),
                }))
            })
            .clone()
    }

    /// Return keeps creation events from the callee but restores the caller's
    /// environment. A callee-created object cannot be established by caller.
    pub(in crate::kernel) fn return_to(&self, caller: &Self) -> Self {
        if self.0.creators.shares_root_with(&caller.0.creators)
            && self.0.pending.shares_root_with(&caller.0.pending)
            && self.0.tainted.shares_root_with(&caller.0.tainted)
            && self.0.authority.shares_roots_with(&caller.0.authority)
            && self.0.anchors.shares_root_with(&caller.0.anchors)
        {
            return caller.clone();
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: caller.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            tainted: self.0.tainted.clone(),
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
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending,
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            tainted: self.0.tainted.clone(),
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
        let mut anchors = self.0.anchors.clone();
        let mut authority = self.0.authority.clone();
        let mut tainted = self.0.tainted.without_key(pending_block);
        if let Some(block) = live_block {
            debug_assert!(matches!(&block, PointerBlock::Heap(_)));
            assert!(
                !creators.contains_key(&block),
                "storage lifetime created twice"
            );
            if let Some(families) = self.0.tainted.get(pending_block) {
                tainted.insert(block.clone(), families.clone());
            }
            let (next, anchor) = authority.allocate_anchor(creator);
            authority = next;
            anchors.insert(block.clone(), anchor);
            creators.insert(block, creator);
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending,
            creators,
            anchors,
            authority,
            tainted,
        }))
    }

    /// Called only at checked C storage creation, never at resource lowering,
    /// contract allocation import, or generic memory-block construction.
    pub(in crate::kernel) fn created(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(block, PointerBlock::Heap(_)) || block.starts_with("local:"));
        let mut creators = self.0.creators.clone();
        assert!(
            !creators.contains_key(&block),
            "storage lifetime created twice"
        );
        let (authority, anchor) = self.0.authority.allocate_anchor(self.0.invocation);
        let mut anchors = self.0.anchors.clone();
        anchors.insert(block.clone(), anchor);
        creators.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            tainted: self.0.tainted.clone(),
        }))
    }

    pub(in crate::kernel) fn created_here(&self, block: &PointerBlock) -> bool {
        self.0.creators.get(block).copied() == Some(self.0.invocation)
    }

    pub(in crate::kernel) fn retirement_refusal(
        &self,
        block: &PointerBlock,
    ) -> Option<CreationRefusal> {
        let anchor = *self.0.anchors.get(block)?;
        self.0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .err()
            .map(CreationRefusal::from)
    }

    /// Once a member existed, absence from the local resource context is no
    /// evidence of an empty population: it may have been transferred away.
    /// This mark follows the storage lifetime across helper calls.
    pub(in crate::kernel) fn member_created(&self, block: &PointerBlock, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        let mut tainted = self.0.tainted.clone();
        let families = tainted
            .get(block)
            .cloned()
            .unwrap_or_default()
            .with_value(family.to_owned());
        tainted.insert(block.clone(), families);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            tainted,
        }))
    }

    /// A checked source fold may establish only at its own creation event,
    /// before any member of this family has existed in the storage lifetime.
    pub(in crate::kernel) fn establish(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        if !self.created_here(block) {
            return Err(CreationRefusal::NotCreationEnvironment);
        }
        if self
            .0
            .tainted
            .get(block)
            .is_some_and(|families| families.contains(&family.to_owned()))
        {
            return Err(CreationRefusal::MembersAlreadyExisted);
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let (authority, _) = self
            .0
            .authority
            .establish(self.0.invocation, anchor, family)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            tainted: self.0.tainted.clone(),
        })))
    }

    pub(in crate::kernel) fn checked_establish(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let after = self.establish(block, description.family())?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: true,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn checked_retire(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let after = self.retire_authority(block, description.family())?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: false,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn retire_authority(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let authority = self
            .0
            .authority
            .retire(self.0.invocation, population)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            tainted: self.0.tainted.clone(),
        })))
    }

    /// End of an automatic or heap lifetime removes its provenance. Future
    /// reuse at the same address needs an independently checked creation.
    pub(in crate::kernel) fn retired(&self, block: &PointerBlock) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let authority = self
            .0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .map_err(CreationRefusal::from)?;
        let mut creators = self.0.creators.clone();
        creators.remove(block);
        let mut anchors = self.0.anchors.clone();
        anchors.remove(block);
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            invocation: self.0.invocation,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            tainted: self.0.tainted.without_key(block),
        })))
    }
}

#[cfg(test)]
mod tests;
