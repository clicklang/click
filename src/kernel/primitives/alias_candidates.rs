//! The entries of a pointer-keyed state collection that an access into
//! one block can alias.
//!
//! Every memory map and heap collection in a `SymbolicMemory` is keyed by a
//! `Address` (or by a key whose ordering starts with one), and `Address`
//! orders by `block` first. `AddressBase` in turn orders by variant:
//!
//! ```text
//! Concrete < StringLiteral < Function < FunctionSymbolic < ExternalArgument
//!          < ExternalObject < Symbolic < Load < PureFunctionApplication
//!          < Heap < Temporary < AutomaticLocal < StaticObject < ContractResult < AggregateReturn < ContractException
//! ```
//!
//! So the entries of one block are one contiguous key range, every
//! `Symbolic` block sits in one contiguous range, and every `Heap` and
//! `Temporary` block precedes the typed `AutomaticLocal` interval.
//!
//! [`AddressBase::proven_distinct`] is the kernel's only structural block
//! separation rule, and it has a shape these ranges follow:
//!
//! * a `Symbolic` block is never distinct from anything, so an access into
//!   one may alias every entry;
//! * two different blocks are distinct whenever either is `Heap` or
//!   `Temporary`, so an access into `Heap(id)` or `Temporary(id)` can only
//!   alias entries in that same block and entries in `Symbolic` blocks;
//! * a loaded pointer is distinct from every heap identity its read's
//!   origin had not handed out, so an access through one can alias the
//!   non-heap blocks, the heap identities that origin holds, and the
//!   temporaries;
//! * two different `Concrete` names are distinct, and a `StringLiteral` is
//!   distinct from every `Concrete` block, so an access into a `Concrete`
//!   block can alias its own block and the non-heap blocks from the
//!   `Function` variant on (`local:` blocks also skip the two external
//!   variants, which are distinct from them), and an access into a
//!   `StringLiteral` block can alias the non-heap blocks from the
//!   `StringLiteral` variant on;
//! * every other access can alias at most the non-heap prefix of the map:
//!   storage the program declares, bounded by source size and not by the
//!   number of allocations.
//!
//! [`AliasCandidates`] names exactly those key ranges. An entry outside them
//! is in a block `proven_distinct` from the access's block, so every alias,
//! containment or overlap question a memory rule asks of it is already
//! answered "separate" by the first rung of its ladder. A rule that keeps
//! such entries (a store, a havoc) or never matches them (an exact-pointer
//! heap lookup) may therefore visit the candidate ranges alone and decide
//! the same thing, at a cost bounded by the storage that can actually alias
//! the access rather than by all of memory. The candidate set is a superset
//! of the non-distinct blocks, never a subset: every rule still asks its own
//! question of every candidate, so a coarser range only costs time.
//!
//! Iteration is in ascending key order and visits each entry at most once,
//! so a "first matching entry" search over the candidates finds the same
//! entry a search over the whole collection would.

use super::{
    Address, AddressBase, AddressOffset, HashedOrdMap, HashedOrdSet, ProgramType, Variable,
};
use std::hash::Hash;
use std::ops::Bound;

/// A state-collection key whose ordering is by address base first.
pub(crate) trait BlockKeyed: Ord + Clone {
    fn key_block(&self) -> &AddressBase;
    /// The smallest key of this type whose block is `block`.
    fn first_key_of(block: &AddressBase) -> Self;
}

impl BlockKeyed for AddressBase {
    fn key_block(&self) -> &AddressBase {
        self
    }

    fn first_key_of(block: &AddressBase) -> Self {
        block.clone()
    }
}

impl BlockKeyed for Address {
    fn key_block(&self) -> &AddressBase {
        &self.base
    }

    fn first_key_of(block: &AddressBase) -> Self {
        // `Constant` is `AddressOffset`'s first variant, so this offset
        // orders below every offset term.
        Address::range_bound(block, AddressOffset::constant(i64::MIN))
    }
}

impl BlockKeyed for (Address, ProgramType) {
    fn key_block(&self) -> &AddressBase {
        &self.0.base
    }

    fn first_key_of(block: &AddressBase) -> Self {
        // `Void` is `ProgramType`'s first variant.
        (Address::first_key_of(block), ProgramType::Void)
    }
}

/// The upper end of one interval of blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Upper {
    /// Up to and including this block.
    Through(AddressBase),
    /// Every block strictly below this one.
    Before(AddressBase),
    Unbounded,
}

impl Upper {
    fn admits(&self, block: &AddressBase) -> bool {
        match self {
            Self::Through(last) => block <= last,
            Self::Before(end) => block < end,
            Self::Unbounded => true,
        }
    }

    /// Whether an interval starting at `start` touches or overlaps one that
    /// ends here, so that the two can be walked as one key range.
    fn reaches(&self, start: Option<&AddressBase>) -> bool {
        match (self, start) {
            (Self::Unbounded, _) => true,
            (_, None) => true,
            (Self::Through(last), Some(start)) => start <= last,
            (Self::Before(end), Some(start)) => start <= end,
        }
    }

    fn max(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unbounded, _) | (_, Self::Unbounded) => Self::Unbounded,
            (Self::Through(left), Self::Through(right)) => Self::Through(left.max(right)),
            (Self::Before(left), Self::Before(right)) => Self::Before(left.max(right)),
            (Self::Through(last), Self::Before(end)) | (Self::Before(end), Self::Through(last)) => {
                if last >= end {
                    Self::Through(last)
                } else {
                    Self::Before(end)
                }
            }
        }
    }
}

/// One interval of blocks: from `start` (inclusive; `None` is the first
/// block) up to `end`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BlockInterval {
    start: Option<AddressBase>,
    end: Upper,
}

impl BlockInterval {
    #[cfg(test)]
    fn contains(&self, block: &AddressBase) -> bool {
        self.start.as_ref().is_none_or(|start| block >= start) && self.end.admits(block)
    }

    fn entries<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a HashedOrdMap<K, V>,
    ) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        let lower = self.start.as_ref().map_or(Bound::Unbounded, |start| {
            Bound::Included(K::first_key_of(start))
        });
        let upper = match &self.end {
            Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
            Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
        };
        map.range::<_, K>((lower, upper))
            .take_while(move |(key, _)| self.end.admits(key.key_block()))
    }

    fn elements<'a, K: BlockKeyed>(
        &'a self,
        set: &'a HashedOrdSet<K>,
    ) -> impl Iterator<Item = &'a K> + 'a {
        let lower = self.start.as_ref().map_or(Bound::Unbounded, |start| {
            Bound::Included(K::first_key_of(start))
        });
        let upper = match &self.end {
            Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
            Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
        };
        set.range::<_, K>((lower, upper))
            .take_while(move |key| self.end.admits(key.key_block()))
    }
}

fn first_string_literal() -> AddressBase {
    AddressBase::StringLiteral {
        identity: crate::kernel::StringLiteralId::new("", 0),
        bytes: Vec::new(),
    }
}

fn first_function() -> AddressBase {
    AddressBase::Function(String::new())
}

fn first_symbolic() -> AddressBase {
    AddressBase::Symbolic(Variable(0))
}

fn first_static() -> AddressBase {
    AddressBase::StaticObject {
        binding: crate::kernel::StaticBindingId::new(
            crate::kernel::StaticBindingOwner::File(None),
            0,
            String::new(),
        ),
    }
}

fn first_heap() -> AddressBase {
    AddressBase::Heap(0)
}

/// The blocks whose entries an access may alias; see the module comment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AliasCandidates {
    /// Ascending, pairwise disjoint and non-adjacent.
    intervals: Vec<BlockInterval>,
}

impl AliasCandidates {
    /// Every block, for a transition with no finite address footprint.
    pub(super) fn every_block() -> Self {
        Self {
            intervals: vec![BlockInterval {
                start: None,
                end: Upper::Unbounded,
            }],
        }
    }

    /// Every block that is not [`AddressBase::proven_distinct`] from
    /// `block`, as a few key ranges (a superset; see the module comment).
    pub(crate) fn of_block(block: &AddressBase) -> Self {
        let own = || BlockInterval {
            start: Some(block.clone()),
            end: Upper::Through(block.clone()),
        };
        let symbolic = || BlockInterval {
            start: Some(first_symbolic()),
            end: Upper::Before(first_heap()),
        };
        let intervals = match block {
            // A loaded pointer may hold any address but that of a heap
            // allocation made after its read.
            AddressBase::Load(load) => {
                if let Some(heap) = crate::kernel::eval::loaded_pointer_read_heap_identities(load) {
                    let mut intervals = vec![BlockInterval {
                        start: None,
                        end: Upper::Before(first_heap()),
                    }];
                    intervals.extend(heap.into_iter().map(|identity| BlockInterval {
                        start: Some(AddressBase::Heap(identity)),
                        end: Upper::Through(AddressBase::Heap(identity)),
                    }));
                    intervals.push(BlockInterval {
                        start: Some(AddressBase::Temporary(0)),
                        end: Upper::Unbounded,
                    });
                    return Self::merged(intervals);
                }
                vec![BlockInterval {
                    start: None,
                    end: Upper::Unbounded,
                }]
            }
            // A symbolic block may be constrained to any address.
            AddressBase::Symbolic(_) | AddressBase::PureFunctionApplication(_) => {
                vec![BlockInterval {
                    start: None,
                    end: Upper::Unbounded,
                }]
            }
            // A fresh identity is distinct from every other identity except
            // a symbolic one.
            AddressBase::Heap(_) | AddressBase::Temporary(_) => vec![symbolic(), own()],
            // Distinct concrete names are distinct; a `local:` block is also
            // distinct from the external variants.
            AddressBase::ContractResult
            | AddressBase::ContractException
            | AddressBase::AggregateReturn { .. }
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::SliceLength { .. }
            | AddressBase::ReferenceCarrier { .. } => vec![
                own(),
                BlockInterval {
                    start: Some(first_function()),
                    end: Upper::Before(AddressBase::ExternalArgument),
                },
                symbolic(),
            ],
            AddressBase::Concrete(_) if block.is_local_block() => {
                vec![
                    own(),
                    BlockInterval {
                        start: Some(first_function()),
                        end: Upper::Before(AddressBase::ExternalArgument),
                    },
                    symbolic(),
                ]
            }
            AddressBase::StaticObject { .. } | AddressBase::Concrete(_) => vec![
                own(),
                BlockInterval {
                    start: Some(first_function()),
                    end: Upper::Before(first_heap()),
                },
            ],
            // A literal is never a declared object.
            AddressBase::StringLiteral { .. } => vec![BlockInterval {
                start: Some(first_string_literal()),
                end: Upper::Before(first_heap()),
            }],
            AddressBase::Function(_) | AddressBase::FunctionSymbolic(_) => vec![
                BlockInterval {
                    start: None,
                    end: Upper::Before(first_heap()),
                },
                BlockInterval {
                    start: Some(AddressBase::Temporary(u64::MAX)),
                    end: Upper::Unbounded,
                },
            ],
            AddressBase::ExternalArgument | AddressBase::ExternalObject(_) => vec![
                BlockInterval {
                    start: None,
                    end: Upper::Before(first_heap()),
                },
                BlockInterval {
                    start: Some(first_static()),
                    end: Upper::Unbounded,
                },
            ],
        };
        Self { intervals }
    }

    /// Exactly the entries of `block`: for a rule that only ever touches
    /// the block it names (retiring one automatic object, forgetting one
    /// field), rather than everything that may alias it.
    pub(crate) fn only_block(block: &AddressBase) -> Self {
        Self {
            intervals: vec![BlockInterval {
                start: Some(block.clone()),
                end: Upper::Through(block.clone()),
            }],
        }
    }

    /// The union of [`Self::of_block`] over several blocks.
    pub(crate) fn of_blocks<'a>(blocks: impl IntoIterator<Item = &'a AddressBase>) -> Self {
        Self::merged(
            blocks
                .into_iter()
                .flat_map(|block| Self::of_block(block).intervals)
                .collect(),
        )
    }

    /// The union of `intervals`, ascending, disjoint and non-adjacent.
    fn merged(mut intervals: Vec<BlockInterval>) -> Self {
        // `None` (the first block) orders first.
        intervals.sort_by(|left, right| left.start.cmp(&right.start));
        let mut merged = Vec::<BlockInterval>::with_capacity(intervals.len());
        for interval in intervals {
            match merged.last_mut() {
                Some(last) if last.end.reaches(interval.start.as_ref()) => {
                    last.end = std::mem::replace(&mut last.end, Upper::Unbounded).max(interval.end);
                }
                _ => merged.push(interval),
            }
        }
        Self { intervals: merged }
    }

    /// Restrict a call's ordinary candidates to blocks outside the atomic
    /// parameter partition, without walking that shared block's cells.
    pub(crate) fn excluding_external_arguments(&self) -> Self {
        let excluded = AddressBase::ExternalArgument;
        // ExternalObject is the next variant, and Variable(0) its first key.
        let after = AddressBase::ExternalObject(Variable(0));
        let mut intervals = Vec::new();
        for interval in &self.intervals {
            if !interval.end.admits(&excluded)
                || interval
                    .start
                    .as_ref()
                    .is_some_and(|start| start > &excluded)
            {
                intervals.push(interval.clone());
                continue;
            }
            if interval
                .start
                .as_ref()
                .is_none_or(|start| start < &excluded)
            {
                intervals.push(BlockInterval {
                    start: interval.start.clone(),
                    end: Upper::Before(excluded.clone()),
                });
            }
            if interval.end.admits(&after) {
                intervals.push(BlockInterval {
                    start: Some(after.clone()),
                    end: interval.end.clone(),
                });
            }
        }
        Self { intervals }
    }

    /// Whether an entry in `block` is among the candidates.
    pub(crate) fn admits_block(&self, block: &AddressBase) -> bool {
        self.intervals.iter().any(|interval| {
            interval.start.as_ref().is_none_or(|start| block >= start) && interval.end.admits(block)
        })
    }

    /// Whether an entry in `block` is among the candidates.
    #[cfg(test)]
    pub(crate) fn contains_block(&self, block: &AddressBase) -> bool {
        self.intervals
            .iter()
            .any(|interval| interval.contains(block))
    }

    /// The candidate entries of `map`, ascending. O(log n) per interval to
    /// position plus the entries visited.
    pub(crate) fn entries<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a HashedOrdMap<K, V>,
    ) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        self.intervals
            .iter()
            .flat_map(move |interval| interval.entries(map))
    }

    /// As `entries`, but seeks past the excluded key ranges of one candidate
    /// block. The ranges and the keys restored within them are in key order.
    pub(super) fn entries_excluding<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a HashedOrdMap<K, V>,
        excluded: &'a [(K, K)],
        restored: &'a [K],
    ) -> impl Iterator<Item = (&'a K, &'a V)> + 'a {
        self.intervals.iter().flat_map(move |interval| {
            let excludes = excluded.first().is_some_and(|(first, _)| {
                let block = first.key_block();
                interval.start.as_ref().is_none_or(|start| start <= block)
                    && interval.end.admits(block)
            });
            let mut lower = interval.start.as_ref().map_or(Bound::Unbounded, |start| {
                Bound::Included(K::first_key_of(start))
            });
            let upper = match &interval.end {
                Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
                Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
            };
            let mut ranges = Vec::new();
            if excludes {
                let mut restored = restored.iter().peekable();
                for (first, last) in excluded {
                    ranges.push((lower, Bound::Excluded(first.clone())));
                    while let Some(key) = restored.next_if(|key| *key <= last) {
                        ranges.push((Bound::Included(key.clone()), Bound::Included(key.clone())));
                    }
                    lower = Bound::Excluded(last.clone());
                }
            }
            ranges.push((lower, upper));
            ranges
                .into_iter()
                .flat_map(move |bounds| map.range::<_, K>(bounds))
                .take_while(move |(key, _)| interval.end.admits(key.key_block()))
        })
    }

    /// The candidate elements of `set`, ascending.
    pub(crate) fn elements<'a, K: BlockKeyed>(
        &'a self,
        set: &'a HashedOrdSet<K>,
    ) -> impl Iterator<Item = &'a K> + 'a {
        self.intervals
            .iter()
            .flat_map(move |interval| interval.elements(set))
    }

    /// Removes the candidate entries `keep` rejects. Entries outside the
    /// candidates are kept without being visited, so this equals
    /// `map.retain(keep)` for any `keep` that accepts every entry in a
    /// block proven distinct from the candidates' blocks. Charges one work
    /// unit per candidate visited.
    pub(crate) fn retain_map<K: BlockKeyed + Hash, V: Clone + Hash>(
        &self,
        map: &mut HashedOrdMap<K, V>,
        mut keep: impl FnMut(&K, &V) -> bool,
    ) {
        let mut visited = 0usize;
        let dropped = self
            .entries(map)
            .inspect(|_| visited += 1)
            .filter(|(key, value)| !keep(key, value))
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(visited);
        for key in dropped {
            map.remove(&key);
        }
    }

    /// The candidate entries of `map` outside the key ranges `kept`
    /// (inclusive, ascending, disjoint), ascending. An entry inside a range
    /// is never visited: meeting the first one re-positions past the range's
    /// end, which costs one position and one entry per range met, so the
    /// iteration costs the entries outside the ranges plus the ranges.
    /// Returns the entries and the number of entries read.
    pub(crate) fn entries_outside<'a, K: BlockKeyed, V>(
        &'a self,
        map: &'a HashedOrdMap<K, V>,
        kept: &[(K, K)],
    ) -> (Vec<(&'a K, &'a V)>, usize) {
        let inside = |key: &K| {
            let position = kept.partition_point(|(low, _)| low <= key);
            position > 0 && key <= &kept[position - 1].1
        };
        let mut entries = Vec::new();
        let mut read = 0usize;
        for interval in &self.intervals {
            let mut lower = interval.start.as_ref().map_or(Bound::Unbounded, |start| {
                Bound::Included(K::first_key_of(start))
            });
            let upper = match &interval.end {
                Upper::Before(end) => Bound::Excluded(K::first_key_of(end)),
                Upper::Through(_) | Upper::Unbounded => Bound::Unbounded,
            };
            'seek: loop {
                // An empty or inverted window would make the range query
                // panic; it holds no entry.
                if let (Bound::Included(low) | Bound::Excluded(low), Bound::Excluded(high)) =
                    (&lower, &upper)
                    && low >= high
                {
                    break;
                }
                for (key, value) in map.range::<_, K>((lower.clone(), upper.clone())) {
                    if !interval.end.admits(key.key_block()) {
                        break 'seek;
                    }
                    read += 1;
                    if inside(key) {
                        let position = kept.partition_point(|(low, _)| low <= key);
                        lower = Bound::Excluded(kept[position - 1].1.clone());
                        continue 'seek;
                    }
                    entries.push((key, value));
                }
                break;
            }
        }
        (entries, read)
    }

    /// [`Self::retain_map`] for a `keep` that the caller has shown accepts
    /// every entry inside the key ranges `kept`: those entries are kept
    /// without being visited ([`Self::entries_outside`]). Charges one work
    /// unit per entry read.
    pub(crate) fn retain_map_outside<K: BlockKeyed + Hash, V: Clone + Hash>(
        &self,
        map: &mut HashedOrdMap<K, V>,
        kept: &[(K, K)],
        mut keep: impl FnMut(&K, &V) -> bool,
    ) {
        let (entries, read) = self.entries_outside(map, kept);
        let dropped = entries
            .into_iter()
            .filter(|(key, value)| !keep(key, value))
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(read);
        for key in dropped {
            map.remove(&key);
        }
    }

    /// [`Self::retain_map`] for a set.
    pub(crate) fn retain_set<K: BlockKeyed + Hash>(
        &self,
        set: &mut HashedOrdSet<K>,
        mut keep: impl FnMut(&K) -> bool,
    ) {
        let mut visited = 0usize;
        let dropped = self
            .elements(set)
            .inspect(|_| visited += 1)
            .filter(|key| !keep(key))
            .cloned()
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(visited);
        for key in dropped {
            set.remove(&key);
        }
    }

    /// Whether some candidate entry satisfies `found`. Equals
    /// `map.iter().any(found)` for any `found` that rejects every entry in a
    /// block proven distinct from the candidates' blocks. Charges one work
    /// unit per candidate visited.
    pub(crate) fn any_entry<K: BlockKeyed, V>(
        &self,
        map: &HashedOrdMap<K, V>,
        mut found: impl FnMut(&K, &V) -> bool,
    ) -> bool {
        let mut visited = 0usize;
        let answer = self.entries(map).any(|(key, value)| {
            visited += 1;
            found(key, value)
        });
        crate::instrumentation::record_deterministic_work(visited);
        answer
    }

    /// [`Self::any_entry`] for a set.
    pub(crate) fn any_element<K: BlockKeyed>(
        &self,
        set: &HashedOrdSet<K>,
        mut found: impl FnMut(&K) -> bool,
    ) -> bool {
        let mut visited = 0usize;
        let answer = self.elements(set).any(|key| {
            visited += 1;
            found(key)
        });
        crate::instrumentation::record_deterministic_work(visited);
        answer
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::OffsetTree;

    fn sample_blocks() -> Vec<AddressBase> {
        vec![
            AddressBase::Concrete("global:g".to_string()),
            AddressBase::Concrete("global:h".to_string()),
            AddressBase::Concrete("local:x".to_string()),
            AddressBase::Concrete("local:y".to_string()),
            AddressBase::Concrete("static:f:s".to_string()),
            AddressBase::StringLiteral {
                identity: crate::kernel::StringLiteralId::new("a", 0),
                bytes: b"one".to_vec(),
            },
            AddressBase::StringLiteral {
                identity: crate::kernel::StringLiteralId::new("b", 0),
                bytes: b"two".to_vec(),
            },
            AddressBase::Function("f".to_string()),
            AddressBase::FunctionSymbolic(Variable(3)),
            AddressBase::ExternalArgument,
            AddressBase::ExternalObject(Variable(4)),
            AddressBase::ExternalObject(Variable(5)),
            AddressBase::Symbolic(Variable(0)),
            AddressBase::Symbolic(Variable(7)),
            AddressBase::PureFunctionApplication(crate::kernel::SharedPureApplication::intern(
                "pick".into(),
                vec![],
            )),
            AddressBase::PureFunctionApplication(crate::kernel::SharedPureApplication::intern(
                "other".into(),
                vec![],
            )),
            AddressBase::Heap(0),
            AddressBase::Heap(1),
            AddressBase::Heap(9),
            AddressBase::Temporary(0),
            AddressBase::Temporary(2),
            AddressBase::ContractResult,
            AddressBase::ContractException,
            AddressBase::AggregateReturn { frame: 0 },
            AddressBase::AggregateReturn { frame: 1 },
            AddressBase::AutomaticLocal {
                binding: crate::kernel::LocalBindingId::new(
                    crate::kernel::LocalFunctionId::new(Some("a.c".into()), "f".into()),
                    false,
                    0,
                    Some("local".into()),
                ),
                instance: crate::kernel::LocalStorageInstance::Implicit,
            },
            AddressBase::StaticObject {
                binding: crate::kernel::StaticBindingId::new(
                    crate::kernel::StaticBindingOwner::File(Some("a.c".into())),
                    0,
                    "value".into(),
                ),
            },
            AddressBase::StaticObject {
                binding: crate::kernel::StaticBindingId::new(
                    crate::kernel::StaticBindingOwner::File(Some("b.c".into())),
                    0,
                    "value".into(),
                ),
            },
            AddressBase::StaticObject {
                binding: crate::kernel::StaticBindingId::new(
                    crate::kernel::StaticBindingOwner::Function(
                        crate::kernel::LocalFunctionId::new(Some("a.c".into()), "f".into()),
                    ),
                    0,
                    "value".into(),
                ),
            },
        ]
    }

    fn cells_of(blocks: &[AddressBase]) -> HashedOrdMap<Address, u32> {
        let mut map = HashedOrdMap::new();
        for (index, block) in blocks.iter().enumerate() {
            for offset in [0, 4, 8] {
                map.insert(
                    Address::new(block.clone(), AddressOffset::constant(offset)),
                    index as u32,
                );
            }
            map.insert(
                Address::new(block.clone(), AddressOffset::variable(Variable(1))),
                index as u32,
            );
        }
        map
    }

    #[test]
    fn candidates_cover_every_block_not_proven_distinct() {
        let blocks = sample_blocks();
        for access in &blocks {
            let candidates = AliasCandidates::of_block(access);
            for other in &blocks {
                if !access.proven_distinct(other) {
                    assert!(
                        candidates.contains_block(other),
                        "{other:?} may alias {access:?} but is not a candidate"
                    );
                }
            }
            assert!(candidates.contains_block(access));
        }
    }

    #[test]
    fn candidates_exclude_unrelated_heap_blocks() {
        let heap = AliasCandidates::of_block(&AddressBase::Heap(1));
        assert!(!heap.contains_block(&AddressBase::Heap(0)));
        assert!(!heap.contains_block(&AddressBase::Temporary(0)));
        assert!(!heap.contains_block(&AddressBase::Concrete("global:g".to_string())));
        assert!(heap.contains_block(&AddressBase::Symbolic(Variable(7))));
        let global = AliasCandidates::of_block(&AddressBase::Concrete("global:g".to_string()));
        assert!(!global.contains_block(&AddressBase::Heap(0)));
        assert!(!global.contains_block(&AddressBase::Concrete("global:h".to_string())));
    }

    #[test]
    fn candidate_iteration_is_the_ascending_filter_of_the_whole_map() {
        let blocks = sample_blocks();
        let map = cells_of(&blocks);
        let mut accesses = blocks
            .iter()
            .map(|block| vec![block.clone()])
            .collect::<Vec<_>>();
        accesses.push(vec![AddressBase::Heap(1), AddressBase::Heap(9)]);
        accesses.push(vec![
            AddressBase::Heap(1),
            AddressBase::Concrete("local:x".to_string()),
        ]);
        accesses.push(vec![
            AddressBase::Concrete("global:g".to_string()),
            AddressBase::Concrete("local:y".to_string()),
            AddressBase::Temporary(2),
        ]);
        accesses.push(vec![
            AddressBase::Heap(0),
            AddressBase::Symbolic(Variable(7)),
        ]);
        for access in &accesses {
            let candidates = AliasCandidates::of_blocks(access);
            let visited = candidates.entries(&map).collect::<Vec<_>>();
            let expected = map
                .iter()
                .filter(|(pointer, _)| candidates.contains_block(&pointer.base))
                .collect::<Vec<_>>();
            assert_eq!(visited, expected, "candidates of {access:?}");
            for block in &blocks {
                if access.iter().any(|access| !access.proven_distinct(block)) {
                    assert!(candidates.contains_block(block));
                }
            }
        }
    }
}
