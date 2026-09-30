//! Persistent pairing of memory occurrences with trusted pointer classes.
//!
//! Equality only selects candidates. Consumption checks the live occurrence's
//! ownership, quantity and coverage in the ordinary resource algebra. Derived
//! roots are excluded from semantic resource equality and fork with the context.
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

/// Only uniform, positive concrete read cores admit a complete predecessor
/// answer. Other shapes retain the existing general read checker until its
/// term and interval indexes are migrated.
fn read_extent(fact: &CResourceFact) -> Option<u64> {
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

#[derive(Clone, Debug, Default)]
struct AddressBucket {
    /// Bucket coordinates can differ from the graph representative. Choosing
    /// the larger payload's coordinates lets merges move only the smaller
    /// resource payload, even when the graph chooses the other representative.
    origin: AffineOffset,
    entries: PersistentMap<(AddressKind, AddressCoordinate), ResourceEntryIds>,
    weight: usize,
    read_shapes: PersistentMap<Option<u64>, usize>,
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
        let mut shape = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(offset) = AffineOffset::of(&pointer.offset) else {
                shape = None;
                continue;
            };
            self.update_coordinate(pointer.block, kind, offset, entry, insert);
        }
        self.update_read_shape(range.base().block.clone(), shape, insert);
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
        let mut shape = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(pointer) = graph.canonical_pointer(&pointer) else {
                shape = None;
                continue;
            };
            self.update_coordinate(pointer.representative, kind, pointer.offset, entry, insert);
        }
        self.update_read_shape(base.representative, shape, insert);
    }

    fn update_read_shape(&mut self, block: PointerBlock, shape: Option<u64>, insert: bool) {
        let mut bucket = self.classes.get(&block).cloned().unwrap_or_default();
        let count = bucket.read_shapes.get(&shape).copied().unwrap_or(0);
        bucket.read_shapes = if insert {
            bucket.read_shapes.with_inserted(shape, count + 1)
        } else if count <= 1 {
            bucket.read_shapes.without_key(&shape)
        } else {
            bucket.read_shapes.with_inserted(shape, count - 1)
        };
        self.classes = if bucket.weight == 0 && bucket.read_shapes.is_empty() {
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
        self.classes = if bucket.weight == 0 && bucket.read_shapes.is_empty() {
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
        for (shape, count) in smaller.read_shapes.iter() {
            let previous = larger.read_shapes.get(shape).copied().unwrap_or(0);
            larger.read_shapes = larger.read_shapes.with_inserted(*shape, previous + count);
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
    addresses: MemoryAddresses,
}

impl ResourceContext {
    /// Pair at proof boundaries, then apply only resource and class deltas.
    /// A restricted or sibling context starts from raw persistent roots;
    /// derived equalities never escape the graph that established them.
    pub(crate) fn synchronize_memory_equalities(&self, assumptions: &PureFactContext) {
        let mut cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let graph = &assumptions.equality_graph;
        if let Some(index) = cache.as_mut()
            && let Some(merges) = graph.pointer_merges_since(&index.graph)
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
                for (entry, insert, fact) in changed.into_iter().rev() {
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
                return;
            }
        }
        let mut addresses = self.storage.index.memory_addresses.clone();
        for merge in graph.pointer_merges() {
            addresses.merge(merge);
        }
        *cache = Some(std::sync::Arc::new(PairedMemoryIndex {
            resources: self.storage.clone(),
            graph: graph.clone(),
            addresses,
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
        index.addresses = addresses;
        index.resources = self.storage.clone();
    }

    /// `Some`, including an empty set, is decisive for the supported read
    /// fragment. `None` selects the existing general checker before lookup;
    /// it is not a retry after an indexed permission or bounds failure.
    pub(super) fn concrete_read_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<Vec<ResourceEntryId>> {
        let graph = &assumptions.equality_graph;
        if graph.has_term_equivalences() || matches!(pointer.block, PointerBlock::LoadedPointer(_))
        {
            return None;
        }
        let point = graph.canonical_pointer(pointer)?;
        if !point.offset.is_constant() {
            return None;
        }
        self.synchronize_memory_equalities(assumptions);
        {
            let cache = self
                .memory_equalities
                .lock()
                .expect("memory equality index");
            let bucket = cache
                .as_ref()?
                .addresses
                .classes
                .get(&point.representative)?;
            if bucket.general_coordinates != 0
                || !bucket.origin.is_constant()
                || bucket.read_shapes.len() != 1
                || bucket.read_shapes.contains_key(&None)
            {
                return None;
            }
        }
        Some(self.equal_address_entries(
            &CMemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), bytes.into(), 1),
            false,
            assumptions,
        ))
    }

    pub(super) fn equal_address_entries(
        &self,
        range: &CMemoryRange,
        owned: bool,
        assumptions: &PureFactContext,
    ) -> Vec<ResourceEntryId> {
        self.synchronize_memory_equalities(assumptions);
        let cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let index = cache.as_ref().expect("paired memory index");
        let mut result = BTreeSet::new();
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
    fn concrete_read_shape_tracks_resource_deltas_and_isolates_forks() {
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
        assert!(mixed.concrete_read_entries(&base, 8, &facts).is_none());
        // A shorter nearest predecessor must not hide the longer view.
        let interior = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(mixed.permits_memory_read(&interior, 4, &facts));
        let restored = mixed.clone().without_exact_representation(&short).unwrap();
        assert!(restored.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(resources.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(mixed.concrete_read_entries(&alias, 8, &facts).is_none());
        assert!(restored.memory_write_range(&alias, 1, &facts).is_none());
    }

    #[test]
    fn uniform_overlapping_views_use_complete_read_predecessors() {
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
}
