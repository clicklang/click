//! Candidate lookup over a context's stated resource compositions.
//!
//! A path states a composition at every call, fold, unfold and store, and
//! keeps each one: `resource_compositions` grows with the path. Separation
//! by ownership asks for a composition holding two given objects as distinct
//! owned members, and scanning every stated composition for one made each
//! such question linear in the path (`issues/scaling.md`). This index names
//! the compositions that can answer instead.
//!
//! **Keys.** A composition is listed under the base and the block of owned
//! memory members, which are exactly the keys a member lookup probes
//! (`ResourceContext::owned_memory_members_with_base`, the block buckets).
//!
//! **Incremental admission.** A snapshot is listed only under the owned
//! members it holds beyond some earlier admitted snapshot, its predecessor:
//! the last one of its own storage origin, read from the storage history, or
//! else the last admitted one or the root when its member index shares
//! enough persistent structure with them that the difference is smaller
//! than the snapshot. Successive snapshots of one resource context, a call's
//! partition beside the frame it was taken from, differ by a few facts, so
//! admission costs what changed, not what the snapshot holds. A snapshot with
//! no such predecessor is listed under all of its owned members. The one exception is the first composition
//! admitted, commonly the function's whole entry frame: it is not listed at
//! all but kept as the `root`, a candidate for every question, whose own
//! member indexes answer it. Holding one composition is then constant work,
//! as `ObjectEvidenceSources` holds its first source.
//!
//! **Completeness for pairs.** Let two members both be held by an admitted
//! snapshot `S`. If `S` has no predecessor, it is listed under both members'
//! keys or is the root, which every question reads. If its predecessor lacks
//! one of the two, `S` is listed under that member's keys. Otherwise the
//! predecessor, admitted earlier, holds both, and the argument repeats on it. A question about a pair
//! that reads the candidates under both members' keys therefore reaches a
//! snapshot holding both whenever any stated composition does. The answer it
//! derives from that snapshot is the one `S` would give: owned members of a
//! valid composition are disjoint, so each object finds the same member.
use super::{CMemoryRange, Pointer, PointerBlock, ResourceContext};
use crate::persistent::{PersistentMap, PersistentSet};

/// How far in size a predecessor candidate may be from the snapshot it
/// lists: each step of distance is two more candidates, each a difference
/// walk of at most the snapshot's size.
const NEAREST_SIZES: usize = 2;

#[derive(Clone, Default)]
pub(in crate::kernel) struct CompositionMemberIndex {
    /// Each admitted composition, by admission ordinal in this context.
    compositions: PersistentMap<u32, ResourceContext>,
    by_base: PersistentMap<Pointer, PersistentSet<u32>>,
    by_block: PersistentMap<PointerBlock, PersistentSet<u32>>,
    /// The last snapshot admitted from each storage origin. Holding it keeps
    /// the origin alive, so its address is never reused as a key.
    checkpoints: PersistentMap<usize, ResourceContext>,
    /// The latest composition admitted with each number of memory facts:
    /// predecessor candidates for a snapshot of another origin, since a
    /// difference walk visits at least the difference in size.
    latest_by_size: PersistentMap<usize, u32>,
    /// The first admitted composition, unlisted; see the module comment.
    root: Option<u32>,
    /// The ordinal the next admitted composition takes.
    next: u32,
}

impl std::fmt::Debug for CompositionMemberIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CompositionMemberIndex")
            .field("compositions", &self.compositions.len())
            .finish()
    }
}

impl CompositionMemberIndex {
    /// Lists `resources`, a composition just stated, under the owned members
    /// it added since the last snapshot of its origin admitted here.
    pub(in crate::kernel) fn admit(&mut self, resources: &ResourceContext) {
        let ordinal = self.next;
        self.next += 1;
        let origin = std::sync::Arc::as_ptr(&resources.storage.origin) as usize;
        let added = self
            .checkpoints
            .get(&origin)
            .and_then(|prior| resources.changed_memory_inputs_from(prior))
            .map(|changed| {
                changed
                    .into_iter()
                    .filter(|fact| resources.contains_exact_representation(fact))
                    .collect::<Vec<_>>()
            })
            .or_else(|| {
                let size = resources.memory_input_facts().len();
                (0..=NEAREST_SIZES)
                    .flat_map(|distance| [size.checked_sub(distance), size.checked_add(distance)])
                    .flatten()
                    .filter_map(|size| self.latest_by_size.get(&size).copied())
                    .chain(self.root)
                    .collect::<std::collections::BTreeSet<_>>()
                    .into_iter()
                    .rev()
                    .filter_map(|prior| self.compositions.get(&prior))
                    .find_map(|prior| added_beyond(prior, resources))
            });
        self.latest_by_size = self
            .latest_by_size
            .with_inserted(resources.memory_input_facts().len(), ordinal);
        self.compositions = self.compositions.with_inserted(ordinal, resources.clone());
        self.checkpoints = self.checkpoints.with_inserted(origin, resources.clone());
        let added = match added {
            Some(added) => added,
            None if self.root.is_none() => {
                self.root = Some(ordinal);
                return;
            }
            None => resources.iter().cloned().collect(),
        };
        for fact in added {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(range) = fact.memory_own_range() {
                self.list(range, ordinal);
            }
        }
    }

    fn list(&mut self, range: &CMemoryRange, ordinal: u32) {
        let base = range.base();
        let at_base = self.by_base.get(base).cloned().unwrap_or_default();
        self.by_base = self
            .by_base
            .with_inserted(base.clone(), at_base.with_value(ordinal));
        let at_block = self.by_block.get(&base.block).cloned().unwrap_or_default();
        self.by_block = self
            .by_block
            .with_inserted(base.block.clone(), at_block.with_value(ordinal));
    }

    /// The admitted compositions listed under any of `bases` or `blocks`, and
    /// the root, in admission order, each once.
    pub(in crate::kernel) fn listed_under<'k>(
        &self,
        bases: impl IntoIterator<Item = &'k Pointer>,
        blocks: impl IntoIterator<Item = &'k PointerBlock>,
    ) -> Vec<&ResourceContext> {
        let mut ordinals = self
            .root
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>();
        let listed = bases
            .into_iter()
            .filter_map(|base| self.by_base.get(base))
            .chain(
                blocks
                    .into_iter()
                    .filter_map(|block| self.by_block.get(block)),
            );
        for set in listed {
            for ordinal in set.iter() {
                crate::instrumentation::record_deterministic_work(1);
                ordinals.insert(*ordinal);
            }
        }
        ordinals
            .into_iter()
            .filter_map(|ordinal| self.compositions.get(&ordinal))
            .collect()
    }
}

/// The memory facts `resources` holds beyond `prior`, when walking the
/// difference of their member indexes costs less than listing `resources`:
/// subtrees the two persistent indexes share are skipped, so a snapshot
/// derived from `prior` by a few changes pays for those changes, and an
/// unrelated one stops after its own size.
fn added_beyond(
    prior: &ResourceContext,
    resources: &ResourceContext,
) -> Option<Vec<super::CResourceFact>> {
    let held = resources.memory_input_facts();
    let mut added = Vec::new();
    for (walked, change) in prior.memory_input_facts().diff(held).enumerate() {
        if walked >= held.len() {
            return None;
        }
        if let super::SnapshotMapChange::Added(fact) = change {
            added.push(fact.clone());
        }
    }
    Some(added)
}
