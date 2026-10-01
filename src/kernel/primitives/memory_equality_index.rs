//! Persistent pairing of memory occurrences with trusted pointer classes.
//!
//! Equality only selects candidates. Consumption checks the live occurrence's
//! ownership, quantity and coverage in the ordinary resource algebra. Derived
//! roots are excluded from semantic resource equality and fork with the context.
#[cfg(test)]
mod cell_tests;
mod read_intervals;
pub(super) mod structural;
use read_intervals::ReadIntervals;

use super::*;
use crate::kernel::equality_graph::{AffineOffset, EqualityGraph, PointerClassMerge};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AddressKind {
    Base,
    OwnedStart,
    ViewedStart,
}

fn range_addresses(range: &CMemoryRange, owned: bool) -> Vec<(AddressKind, Pointer)> {
    let mut addresses = vec![(
        if owned {
            AddressKind::OwnedStart
        } else {
            AddressKind::ViewedStart
        },
        range
            .base()
            .offset_by_elements(range.start().clone(), range.element_width()),
    )];
    // Concrete spans use their start index, so one base with thousands of
    // disjoint ranges never creates a thousand-entry exact-base candidate set.
    if range.start().as_const().is_none() || range.end().as_const().is_none() {
        addresses.push((AddressKind::Base, range.base().clone()));
    }
    addresses
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AddressCoordinate(AffineOffset);
impl Ord for AddressCoordinate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.address_order(&other.0)
    }
}
impl PartialOrd for AddressCoordinate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Positive concrete read cores contribute physical byte intervals.
/// Unsupported entries are counted too, so incomplete coverage selects the
/// existing general checker before lookup.
pub(super) fn read_extent(fact: &CResourceFact) -> Option<u64> {
    if let CResourceFact::Own(_, quantity) = fact
        && !quantity.as_const().is_some_and(|value| (value as i32) > 0)
    {
        return None;
    }
    let range = fact.memory_range()?;
    let start = range.start().as_const()? as i32;
    let end = range.end().as_const()? as i32;
    let count = u64::try_from(i64::from(end) - i64::from(start)).ok()?;
    let width = u64::from(range.element_width());
    let extent = count.checked_mul(width)?;
    (extent > 0).then_some(extent)
}

// Whole-cell candidates carry their own authorized read footprints. The existing int32-slot interpretation of pointer reads is special:
// eight bytes may read one logical four-byte element, including an interior
// element of a longer range. Those partial reads retain the range checker.
fn exact_access_sizes(fact: &CResourceFact) -> Vec<u32> {
    let Some(extent) = read_extent(fact).and_then(|extent| u32::try_from(extent).ok()) else {
        return Vec::new();
    };
    let width = fact.memory_range().expect("memory extent").element_width();
    match (extent, width) {
        (8, 4) => Vec::new(),
        (4, 4) => vec![4, 8],
        _ => vec![extent],
    }
}

#[derive(Clone, Debug, Default)]
struct AddressBucket {
    /// Bucket coordinates can differ from the graph representative. Choosing
    /// the larger payload's coordinates lets merges move only the smaller
    /// resource payload, even when the graph chooses the other representative.
    origin: AffineOffset,
    entries: PersistentMap<(AddressKind, AddressCoordinate), ResourceEntryIds>,
    weight: usize,
    read_intervals: ReadIntervals,
    memory_count: usize,
    general_coordinates: usize,
}

#[derive(Clone, Debug, Default)]
pub(super) struct MemoryAddresses {
    classes: PersistentMap<PointerBlock, AddressBucket>,
}

impl MemoryAddresses {
    pub(super) fn update(
        &mut self,
        range: &CMemoryRange,
        owned: bool,
        entry: ResourceEntryId,
        insert: bool,
        fact: &CResourceFact,
    ) {
        let extent = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(offset) = AffineOffset::of(&pointer.offset) else {
                continue;
            };
            self.update_coordinate(pointer.block, kind, offset, entry, insert, extent);
        }
        self.update_memory_count(range.base().block.clone(), insert);
    }

    fn update_in_graph(
        &mut self,
        range: &CMemoryRange,
        owned: bool,
        entry: ResourceEntryId,
        insert: bool,
        graph: &EqualityGraph,
        fact: &CResourceFact,
    ) {
        // Track unsupported offsets too: they must prevent a decisive
        // indexed miss, even when they contribute no address row.
        let Some(base) = graph.canonical_pointer(&Pointer {
            block: range.base().block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        }) else {
            return;
        };
        let extent = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(pointer) = graph.canonical_pointer(&pointer) else {
                continue;
            };
            self.update_coordinate(
                pointer.representative,
                kind,
                pointer.offset,
                entry,
                insert,
                extent,
            );
        }
        self.update_memory_count(base.representative, insert);
    }

    fn update_memory_count(&mut self, block: PointerBlock, insert: bool) {
        let mut bucket = self.classes.get(&block).cloned().unwrap_or_default();
        if insert {
            bucket.memory_count += 1;
        } else {
            bucket.memory_count -= 1;
        }
        self.classes = if bucket.weight == 0 && bucket.memory_count == 0 {
            self.classes.without_key(&block)
        } else {
            self.classes.with_inserted(block, bucket)
        };
    }

    fn update_coordinate(
        &mut self,
        block: PointerBlock,
        kind: AddressKind,
        offset: AffineOffset,
        entry: ResourceEntryId,
        insert: bool,
        read_extent: Option<u64>,
    ) {
        let mut bucket = self.classes.get(&block).cloned().unwrap_or_default();
        let Some(key) = offset.checked_add(&bucket.origin) else {
            return;
        };
        let general = kind == AddressKind::Base || !key.is_constant();
        let key = (kind, AddressCoordinate(key));
        let entries = bucket.entries.get(&key).cloned().unwrap_or_default();
        let present = entries.contains(&entry);
        if insert == present {
            return;
        }
        if key.0 != AddressKind::Base
            && let Some(extent) = read_extent
        {
            if insert {
                if let Some(end) = key
                    .1
                    .0
                    .checked_add(&AffineOffset::constant(i128::from(extent)))
                {
                    bucket
                        .read_intervals
                        .insert(key.1.clone(), AddressCoordinate(end), entry);
                }
            } else {
                bucket.read_intervals.remove(key.1.clone(), entry);
            }
        }
        if insert {
            bucket.entries = bucket.entries.with_inserted(key, entries.with_value(entry));
            bucket.weight += 1;
            bucket.general_coordinates += usize::from(general);
        } else {
            let entries = entries.without_value(&entry);
            bucket.entries = if entries.is_empty() {
                bucket.entries.without_key(&key)
            } else {
                bucket.entries.with_inserted(key, entries)
            };
            bucket.weight -= 1;
            bucket.general_coordinates -= usize::from(general);
        }
        self.classes = if bucket.weight == 0 && bucket.memory_count == 0 {
            self.classes.without_key(&block)
        } else {
            self.classes.with_inserted(block, bucket)
        };
    }

    fn merge(&mut self, merge: PointerClassMerge) {
        let Some(moved) = self.classes.get(&merge.moved).cloned() else {
            return;
        };
        let kept = self.classes.get(&merge.kept).cloned().unwrap_or_default();
        self.classes = self.classes.without_key(&merge.moved);
        let (mut larger, smaller, shift) = if moved.weight <= kept.weight {
            let Some(shift) = merge
                .moved_from_kept
                .checked_add(&kept.origin)
                .and_then(|value| value.checked_sub(&moved.origin))
            else {
                return;
            };
            (kept, moved, shift)
        } else {
            let Some(origin) = moved.origin.checked_sub(&merge.moved_from_kept) else {
                return;
            };
            let Some(shift) = origin.checked_sub(&kept.origin) else {
                return;
            };
            let mut moved = moved;
            moved.origin = origin;
            (moved, kept, shift)
        };
        larger.memory_count += smaller.memory_count;
        for (start, end, entry) in smaller.read_intervals.iter() {
            let Some(start) = start.0.checked_add(&shift) else {
                continue;
            };
            let Some(end) = end.0.checked_add(&shift) else {
                continue;
            };
            larger
                .read_intervals
                .insert(AddressCoordinate(start), AddressCoordinate(end), entry);
        }
        for ((kind, offset), entries) in smaller.entries.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let Some(offset) = offset.0.checked_add(&shift) else {
                continue;
            };
            let general = *kind == AddressKind::Base || !offset.is_constant();
            let offset = (kind.clone(), AddressCoordinate(offset));
            let mut combined = larger.entries.get(&offset).cloned().unwrap_or_default();
            for entry in entries.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if !combined.contains(entry) {
                    combined = combined.with_value(*entry);
                    larger.weight += 1;
                    larger.general_coordinates += usize::from(general);
                }
            }
            larger.entries = larger.entries.with_inserted(offset, combined);
        }
        self.classes = self.classes.with_inserted(merge.kept, larger);
    }
}

#[derive(Clone)]
pub(super) struct PairedMemoryIndex {
    resources: std::sync::Arc<ResourceContextStorage>,
    graph: EqualityGraph,
    source_identity: std::sync::Arc<()>,
    addresses: MemoryAddresses,
    points: AddressPoints,
    pending_points: PersistentMap<ResourceEntryId, CResourceFact>,
    points_initialized: bool,
}

/// A payload attached to typed address classes in the trusted graph. It has
/// no equality solver of its own: graph merges move only affected entries.
#[derive(Clone, Default)]
struct AddressPointBucket {
    // Fold selection considers every occurrence. Reads select only entries
    // with the requested checked footprint, independent of other shapes at
    // this address or elsewhere in the pointer-block class.
    entries: ResourceEntryIds,
    reads: PersistentMap<u32, ResourceEntryIds>,
    // Writes require their own payload: a read footprint may contain only
    // views, even when a larger owner shares the same start address.
    writes: PersistentMap<u32, ResourceEntryIds>,
}

#[derive(Clone, Default)]
struct AddressPoints {
    classes: PersistentMap<u64, AddressPointBucket>,
    entries: PersistentMap<ResourceEntryId, u64>,
}
impl AddressPoints {
    fn merge(&mut self, moved: u64, kept: u64) {
        let Some(mut smaller) = self.classes.get(&moved).cloned() else {
            return;
        };
        let mut larger = self.classes.get(&kept).cloned().unwrap_or_default();
        self.classes.remove(&moved);
        if larger.entries.len() < smaller.entries.len() {
            std::mem::swap(&mut larger, &mut smaller);
        }
        for entry in smaller.entries.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.entries = larger.entries.with_value(*entry);
        }
        // Each occurrence contributes at most two footprints per access kind. Using the
        // same smaller occurrence payload for both indexes bounds all moves,
        // even when the graph chooses the other class representative.
        for (larger_access, smaller_access) in [
            (&mut larger.reads, &smaller.reads),
            (&mut larger.writes, &smaller.writes),
        ] {
            for (bytes, entries) in smaller_access.iter() {
                let mut combined = larger_access.get(bytes).cloned().unwrap_or_default();
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    combined = combined.with_value(*entry);
                }
                larger_access.insert(*bytes, combined);
            }
        }
        self.classes.insert(kept, larger);
    }
    fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        fact: &CResourceFact,
        graph: &EqualityGraph,
    ) {
        let Some(range) = fact.memory_range() else {
            return;
        };
        let class = if insert {
            let start = range
                .base()
                .offset_by_elements(range.start().clone(), range.element_width());
            let Some(class) = graph.address_class(&start) else {
                return;
            };
            self.entries.insert(entry, class);
            class
        } else {
            let Some(class) = self.entries.get(&entry).copied() else {
                return;
            };
            self.entries.remove(&entry);
            graph.address_class_root(class)
        };
        let mut bucket = self.classes.get(&class).cloned().unwrap_or_default();
        bucket.entries = if insert {
            bucket.entries.with_value(entry)
        } else {
            bucket.entries.without_value(&entry)
        };
        let sizes = exact_access_sizes(fact);
        for access in
            std::iter::once(&mut bucket.reads).chain(fact.is_own().then_some(&mut bucket.writes))
        {
            for bytes in &sizes {
                let entries = access.get(bytes).cloned().unwrap_or_default();
                let entries = if insert {
                    entries.with_value(entry)
                } else {
                    entries.without_value(&entry)
                };
                if entries.is_empty() {
                    access.remove(bytes);
                } else {
                    access.insert(*bytes, entries);
                }
            }
        }
        if bucket.entries.is_empty() {
            self.classes.remove(&class);
        } else {
            self.classes.insert(class, bucket);
        }
    }
}

pub(super) enum MemoryAccessEntries {
    Intervals(read_intervals::CoveringIntervals),
    Exact(crate::persistent::OwnedSetValues<ResourceEntryId>),
    Structural(std::collections::btree_set::IntoIter<ResourceEntryId>),
}
impl Iterator for MemoryAccessEntries {
    type Item = ResourceEntryId;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Intervals(entries) => entries.next(),
            Self::Exact(entries) => entries.next(),
            Self::Structural(entries) => entries.next(),
        }
    }
}
impl MemoryAccessEntries {
    pub(super) fn exact(&self) -> bool {
        matches!(self, Self::Exact(_))
    }
}

impl ResourceContext {
    /// Pair at proof boundaries, then apply only resource and class deltas.
    /// A restricted or sibling context starts from raw persistent roots;
    /// derived equalities never escape the graph that established them.
    pub(crate) fn synchronize_memory_equalities(&self, assumptions: &PureFactContext) {
        self.pair_memory_equalities(assumptions, true);
    }

    // A lookup cannot turn a previously unpaired frame into a full-input
    // registration pass. Input registration belongs to the execution proof
    // boundary above; cold kernel queries retain the affine index/general
    // checker until that boundary has published complete address coverage.
    fn pair_memory_equalities(&self, assumptions: &PureFactContext, register_input: bool) {
        let mut cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let graph = &assumptions.equality_graph;
        if let Some(index) = cache.as_mut()
            && (!register_input || index.points_initialized)
            && graph.pointer_merges_since(&index.graph).is_some()
            && graph.address_merges_since(&index.graph).is_some()
            && std::sync::Arc::ptr_eq(&self.storage.origin, &index.resources.origin)
        {
            let index = std::sync::Arc::make_mut(index);
            let expected = index.resources.history.as_ref();
            let mut cursor = self.storage.history.as_ref();
            let mut changed = Vec::new();
            let mut descendant = true;
            while !Self::history_tail_is(cursor, expected) {
                let Some(change) = cursor else {
                    descendant = false;
                    break;
                };
                crate::instrumentation::record_deterministic_work(1);
                if let Some((entry, insert)) = change.entry_delta {
                    changed.push((entry, insert, change.fact.clone()));
                }
                cursor = change.parent.as_ref();
            }
            if descendant {
                for (_, fact) in index.pending_points.iter() {
                    if let Some(range) = fact.memory_range() {
                        graph.address_class(
                            &range
                                .base()
                                .offset_by_elements(range.start().clone(), range.element_width()),
                        );
                    }
                }
                // Registration may itself close congruent loaded addresses.
                // Finish it before reading either stream of graph deltas.
                for (_, insert, fact) in changed.iter().rev() {
                    if index.points_initialized
                        && *insert
                        && let Some(range) = fact.memory_range()
                    {
                        graph.address_class(
                            &range
                                .base()
                                .offset_by_elements(range.start().clone(), range.element_width()),
                        );
                    }
                }
                let merges = graph
                    .pointer_merges_since(&index.graph)
                    .expect("pointer prefix");
                for merge in graph
                    .address_merges_since(&index.graph)
                    .expect("address prefix")
                {
                    index.points.merge(merge.moved, merge.kept);
                }
                for (entry, fact) in index.pending_points.iter() {
                    index.points.update(*entry, true, fact, graph);
                }
                index.pending_points = PersistentMap::default();
                for (entry, insert, fact) in changed.into_iter().rev() {
                    if index.points_initialized {
                        index.points.update(entry, insert, &fact, graph);
                    }
                    let Some(range) = fact.memory_range() else {
                        continue;
                    };
                    index.addresses.update_in_graph(
                        range,
                        fact.is_own(),
                        entry,
                        insert,
                        &index.graph,
                        &fact,
                    );
                }
                for merge in merges {
                    index.addresses.merge(merge);
                }
                index.resources = self.storage.clone();
                index.graph = graph.clone();
                index.source_identity = graph.registration_identity();
                return;
            }
        }
        let mut points = AddressPoints::default();
        // Establish the pairing once at the input boundary. Ordinary proof
        // steps inherit these persistent roots and apply only entry deltas.
        // Register the entire input before assigning any class-keyed payload.
        if register_input {
            for (_, fact) in self.storage.facts.iter() {
                if let Some(range) = fact.memory_range() {
                    graph.address_class(
                        &range
                            .base()
                            .offset_by_elements(range.start().clone(), range.element_width()),
                    );
                }
            }
            for (entry, fact) in self.storage.facts.iter() {
                points.update(*entry, true, fact, graph);
            }
        }
        let mut addresses = self.storage.index.memory_addresses.clone();
        for merge in graph.pointer_merges() {
            addresses.merge(merge);
        }
        *cache = Some(std::sync::Arc::new(PairedMemoryIndex {
            resources: self.storage.clone(),
            graph: graph.clone(),
            source_identity: graph.registration_identity(),
            addresses,
            points,
            pending_points: PersistentMap::default(),
            points_initialized: register_input,
        }));
    }

    /// Full resource normalization already visits its complete input. Rebuild
    /// the derived payload there, using the retained graph checkpoint rather
    /// than processing unrelated equality history at the next simple tactic.
    pub(super) fn rebuild_paired_memory_entries(&self) {
        let mut cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let Some(index) = cache.as_mut() else { return };
        let index = std::sync::Arc::make_mut(index);
        let mut addresses = MemoryAddresses::default();
        for (entry, fact) in self.storage.facts.iter() {
            let Some(range) = fact.memory_range() else {
                continue;
            };
            addresses.update_in_graph(range, fact.is_own(), *entry, true, &index.graph, fact);
        }
        // Normalization may renumber occurrences. Retain its published root
        // as an explicit pairing delta, and register it on the source graph at
        // the next boundary rather than mutating the private checkpoint clone.
        index.points = AddressPoints::default();
        index.pending_points = if index.points_initialized {
            self.storage.facts.clone()
        } else {
            PersistentMap::default()
        };
        index.addresses = addresses;
        index.resources = self.storage.clone();
    }

    fn pair_for_query(&self, assumptions: &PureFactContext) -> Option<Self> {
        let source = assumptions.equality_graph.registration_identity();
        let scratch = self
            .memory_equalities
            .lock()
            .expect("memory equality index")
            .as_ref()
            .is_some_and(|index| !std::sync::Arc::ptr_eq(&index.source_identity, &source));
        if scratch {
            // Fork only persistent roots. A transient query cannot replace the
            // published input checkpoint; queries on its owning graph still
            // advance that checkpoint, avoiding repeated accumulated deltas.
            let local = self.clone();
            local.pair_memory_equalities(assumptions, false);
            Some(local)
        } else {
            self.pair_memory_equalities(assumptions, false);
            None
        }
    }

    /// Concrete interval coverage supports decisive hits and misses. Exact
    /// whole-cell payloads supply eligible known-equal occurrences; a missing
    /// footprint is unknown when containment, arithmetic or snapshot reasoning
    /// could apply.
    /// `None` selects the existing checker before any permission check; a
    /// failed permission or bounds check is never retried.
    pub(super) fn concrete_read_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<MemoryAccessEntries> {
        self.concrete_access_entries(pointer, bytes, assumptions, false)
    }

    /// Owned whole-cell matches or complete affine interval candidates for
    /// writes. Read payloads are unsuitable: a matching view could hide an owner.
    /// `None` selects the general checker before testing any candidate.
    pub(super) fn concrete_write_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<MemoryAccessEntries> {
        self.concrete_access_entries(pointer, bytes, assumptions, true)
    }

    fn concrete_access_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
        owned: bool,
    ) -> Option<MemoryAccessEntries> {
        let graph = &assumptions.equality_graph;
        let class = graph.address_class(pointer)?;
        let local = self.pair_for_query(assumptions);
        let paired = local.as_ref().unwrap_or(self);
        let cache = paired
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let index = cache.as_ref()?;
        if index.points_initialized {
            let class = graph.address_class_root(class);
            let entries = index
                .points
                .classes
                .get(&class)
                .and_then(|bucket| if owned { &bucket.writes } else { &bucket.reads }.get(&bytes))
                .cloned()
                .unwrap_or_default();
            // A graph answer is equality or unknown, not disequality. Scalar
            // arithmetic and snapshot transport can justify an access outside
            // this address closure, so an unbound class selects the existing
            // checker before any permission check. A bound whole-cell class
            // supplies checked address evidence and needs no spelling search.
            // Writes select only positive concrete owners under the same
            // footprint/width eligibility rule; views never enter that payload.
            if !entries.is_empty() {
                return Some(MemoryAccessEntries::Exact(entries.owned_values()));
            }
        }
        let point = graph.canonical_pointer(pointer)?;
        let bucket = index.addresses.classes.get(&point.representative)?;
        if graph.has_non_affine_term_equivalences()
            || matches!(pointer.block, PointerBlock::LoadedPointer(_))
            || !point.offset.is_constant()
        {
            return None;
        }
        if bucket.general_coordinates != 0
            || !bucket.origin.is_constant()
            || bucket.read_intervals.len() != bucket.memory_count
        {
            return None;
        }
        let start = point.offset.checked_add(&bucket.origin)?;
        let candidate_bytes = crate::kernel::assumptions::read_candidate_byte_width(bytes);
        let end = start.checked_add(&AffineOffset::constant(i128::from(candidate_bytes)))?;
        Some(MemoryAccessEntries::Intervals(
            bucket
                .read_intervals
                .covering(&AddressCoordinate(start), &AddressCoordinate(end)),
        ))
    }

    pub(super) fn equal_address_entries(
        &self,
        range: &CMemoryRange,
        owned: bool,
        assumptions: &PureFactContext,
    ) -> Vec<ResourceEntryId> {
        let start = range
            .base()
            .offset_by_elements(range.start().clone(), range.element_width());
        let point_class = assumptions.equality_graph.address_class(&start);
        let local = self.pair_for_query(assumptions);
        let paired = local.as_ref().unwrap_or(self);
        let cache = paired
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let index = cache.as_ref().expect("paired memory index");
        let mut result = BTreeSet::new();
        if let Some(class) = point_class {
            let class = assumptions.equality_graph.address_class_root(class);
            if let Some(bucket) = index.points.classes.get(&class) {
                result.extend(bucket.entries.iter().copied());
            }
        }
        let start = range
            .base()
            .offset_by_elements(range.start().clone(), range.element_width());
        let end = range
            .base()
            .offset_by_elements(range.end().clone(), range.element_width());
        let mut addresses = vec![
            (AddressKind::Base, range.base().clone()),
            (
                if owned {
                    AddressKind::OwnedStart
                } else {
                    AddressKind::ViewedStart
                },
                start.clone(),
            ),
        ];
        if !owned {
            addresses.push((AddressKind::OwnedStart, start));
        }
        for (kind, address) in addresses {
            let Some(pointer) = assumptions.equality_graph.canonical_pointer(&address) else {
                continue;
            };
            let Some(bucket) = index.addresses.classes.get(&pointer.representative) else {
                continue;
            };
            let Some(offset) = pointer.offset.checked_add(&bucket.origin) else {
                continue;
            };
            let key = (kind.clone(), AddressCoordinate(offset));
            if let Some(entries) = bucket.entries.get(&key) {
                result.extend(entries.iter().copied());
            }
            if kind == AddressKind::Base
                || range.start().as_const().is_none()
                || range.end().as_const().is_none()
            {
                continue;
            }
            // Visit a predecessor and starts inside the explicitly required
            // span. Coverage checks reject a predecessor ending before it.
            if let Some(((previous_kind, previous), entries)) = bucket.entries.get_less_than(&key)
                && *previous_kind == kind
                && key.1.0.constant_difference(&previous.0).is_some()
            {
                result.extend(entries.iter().copied());
            }
            let Some(end) = assumptions.equality_graph.canonical_pointer(&end) else {
                continue;
            };
            let Some(end_offset) = end.offset.checked_add(&bucket.origin) else {
                continue;
            };
            let mut cursor = key;
            while let Some((next, entries)) = bucket.entries.get_greater_than(&cursor) {
                if next.0 != kind
                    || !end_offset
                        .constant_difference(&next.1.0)
                        .is_some_and(|difference| difference > 0)
                {
                    break;
                }
                crate::instrumentation::record_deterministic_work(1);
                result.extend(entries.iter().copied());
                cursor = next.clone();
            }
        }
        result.into_iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn view(base: &Pointer, start: u32, end: u32) -> CResourceFact {
        CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            start.into(),
            end.into(),
            1,
        ))
    }

    #[test]
    fn concrete_read_coverage_tracks_resource_deltas_and_isolates_forks() {
        let base = Pointer::symbolic(Variable(851_000));
        let alias = Pointer::symbolic(Variable(851_001));
        let empty = PureFactContext::new();
        let resources = ResourceContext::new().unchecked_with_fact(view(&base, 0, 8));
        resources.synchronize_memory_equalities(&empty);
        let facts = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
        assert!(resources.permits_memory_read(&alias, 8, &facts));
        assert!(!resources.permits_memory_read(&alias, 9, &facts));
        assert!(!resources.permits_memory_read(&alias, 1, &empty));
        let short = view(&base, 2, 4);
        let mixed = resources.clone().unchecked_with_fact(short.clone());
        assert!(mixed.concrete_read_entries(&base, 8, &facts).is_some());
        // A shorter nearest predecessor must not hide the longer view.
        let interior = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(mixed.permits_memory_read(&interior, 4, &facts));
        let restored = mixed.clone().without_exact_representation(&short).unwrap();
        assert!(restored.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(resources.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(mixed.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(restored.memory_write_range(&alias, 1, &facts).is_none());
    }

    #[test]
    fn overlapping_views_use_complete_read_intervals() {
        let base = Pointer::symbolic(Variable(851_010));
        let facts = PureFactContext::new();
        let resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 8))
            .unchecked_with_fact(view(&base, 4, 12));
        let at = |offset| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        assert!(resources.concrete_read_entries(&at(6), 6, &facts).is_some());
        assert!(resources.permits_memory_read(&at(6), 6, &facts));
        assert!(!resources.permits_memory_read(&at(6), 7, &facts));
        assert!(!resources.permits_memory_read(&at(12), 1, &facts));
    }

    #[test]
    fn write_intervals_preserve_authority_coverage_and_branch_isolation() {
        let base = Pointer::symbolic(Variable(861_000));
        let middle = Pointer::symbolic(Variable(861_001));
        let alias = Pointer::symbolic(Variable(861_002));
        let owned_range =
            CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), 32u32.into(), 1);
        let owned = CResourceFact::own_memory(owned_range.clone());
        // An exact-size view must neither grant writes nor hide a longer owner.
        let short = view(&base, 8, 12);
        let resources = ResourceContext::new()
            .unchecked_with_fact(owned.clone())
            .unchecked_with_fact(short.clone());
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let sibling = resources.clone();
        let displaced = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let facts = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(displaced, middle.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
        assert!(
            resources
                .concrete_write_entries(&alias, 4, &facts)
                .is_some()
        );
        assert_eq!(
            resources.memory_write_range(&alias, 4, &facts),
            Some(&owned_range)
        );
        assert_eq!(
            resources.memory_write_range(&alias, 24, &facts),
            Some(&owned_range)
        );
        assert!(resources.memory_write_range(&alias, 25, &facts).is_none());
        assert!(sibling.memory_write_range(&alias, 4, &empty).is_none());
        let views = resources
            .clone()
            .without_exact_representation(&owned)
            .unwrap();
        assert!(views.permits_memory_read(&alias, 4, &facts));
        assert!(views.memory_write_range(&alias, 4, &facts).is_none());
        let restored = views.unchecked_with_fact(owned);
        assert_eq!(
            restored.memory_write_range(&alias, 24, &facts),
            Some(&owned_range)
        );
    }

    #[test]
    fn pointer_slot_candidates_preserve_the_checked_logical_width_rule() {
        let base = Pointer::symbolic(Variable(851_015));
        let facts = PureFactContext::new();
        let slot = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new(base.clone(), 0u32.into(), 1u32.into()),
        ));
        assert!(slot.permits_memory_read(&base, C_POINTER_BYTE_WIDTH, &facts));
        assert!(!slot.permits_memory_read(&base, 16, &facts));
        assert!(
            slot.memory_write_range(&base, C_POINTER_BYTE_WIDTH, &facts)
                .is_some()
        );
        assert!(slot.memory_write_range(&base, 16, &facts).is_none());
        // Candidate selection is an overapproximation. The logical rule does
        // not authorize a pointer read from a four-byte, byte-indexed view.
        let bytes = ResourceContext::new().unchecked_with_fact(view(&base, 0, 4));
        assert!(!bytes.permits_memory_read(&base, C_POINTER_BYTE_WIDTH, &facts));
        let byte_owner = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        assert!(
            byte_owner
                .memory_write_range(&base, C_POINTER_BYTE_WIDTH, &facts)
                .is_none()
        );
    }

    #[test]
    fn mixed_extent_reads_find_covering_view_hidden_by_shorter_predecessor() {
        let base = Pointer::symbolic(Variable(851_020));
        let alias = Pointer::symbolic(Variable(851_021));
        let empty = PureFactContext::new();
        let resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 32))
            .unchecked_with_fact(view(&base, 4, 8));
        resources.synchronize_memory_equalities(&empty);
        let middle = Pointer::symbolic(Variable(851_022));
        let displaced = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let facts = empty
            .assume_condition(
                ConditionTerm::pointer_equal(displaced, middle.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
        let interior = Pointer {
            block: alias.block,
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(
            resources
                .concrete_read_entries(&interior, 20, &facts)
                .is_some()
        );
        assert!(resources.permits_memory_read(&interior, 20, &facts));
        assert!(!resources.permits_memory_read(&interior, 21, &facts));
        let without_long = resources
            .clone()
            .without_exact_representation(&view(&base, 0, 32))
            .unwrap();
        assert!(!without_long.permits_memory_read(&interior, 1, &facts));
        assert!(resources.permits_memory_read(&interior, 20, &facts));
    }

    #[test]
    fn mixed_extent_read_hits_and_misses_do_not_scan_unrelated_ranges() {
        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024] {
            let base = Pointer::symbolic(Variable(851_030));
            let alias = Pointer::symbolic(Variable(851_031));
            let mut resources = ResourceContext::new()
                .unchecked_with_fact(view(&base, 0, 4))
                .unchecked_with_fact(view(&base, 1, 2));
            for index in 1..=size {
                resources = resources.unchecked_with_fact(view(
                    &base,
                    index * 8,
                    index * 8 + 1 + index % 2,
                ));
            }
            let empty = PureFactContext::new();
            resources.synchronize_memory_equalities(&empty);
            let facts =
                empty.assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
            resources.synchronize_memory_equalities(&facts);
            let at = |offset| Pointer {
                block: alias.block.clone(),
                offset: PointerOffsetTerm::Constant(offset),
            };
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert_eq!(
                        resources
                            .concrete_read_entries(&at(2), 2, &facts)
                            .unwrap()
                            .count(),
                        1
                    );
                    assert!(resources.permits_memory_read(&at(2), 2, &facts));
                    assert!(!resources.permits_memory_read(&at(4), 1, &facts));
                    assert!(!resources.permits_memory_read(&at(2), 3, &facts));
                })
            });
            samples.push((size, work, map_work));
        }
        assert!(
            samples[3].1 <= samples[0].1 * 2 + 32,
            "read checker scanned unrelated ranges: {samples:?}"
        );
        assert!(
            samples[3].2 <= samples[0].2 * 3 + 128,
            "interval lookup scanned unrelated ranges: {samples:?}"
        );
    }

    #[test]
    fn a_read_does_not_materialize_all_covering_views() {
        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024] {
            let base = Pointer::symbolic(Variable(851_040));
            let facts = PureFactContext::new();
            let mut resources = ResourceContext::new();
            for end in 1..=size {
                resources = resources.unchecked_with_fact(view(&base, 0, end));
            }
            resources.synchronize_memory_equalities(&facts);
            let (allowed, work) = crate::persistent::measure_persistent_work(|| {
                resources.permits_memory_read(&base, 1, &facts)
            });
            assert!(allowed);
            samples.push((size, work));
        }
        assert!(
            samples[3].1 <= samples[0].1 * 2 + 32,
            "a read enumerated every covering view: {samples:?}"
        );
    }
}
