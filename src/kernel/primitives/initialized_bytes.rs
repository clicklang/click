//! The bytes of storage with an initialization history that a C store has
//! initialized, kept apart from the cached cell values.
//!
//! Automatic storage and fresh `malloc` storage start out uninitialized, and a
//! read of a byte no store has written is undefined. A cached cell is
//! evidence that its bytes were written, but a cell is a *value*, and values
//! are forgotten for reasons that have nothing to do with initialization: a
//! store the facts cannot place, a loop or call havoc, a join. A store only
//! ever initializes bytes, so none of those events makes an initialized byte
//! uninitialized again. This record is what survives them: the value is gone,
//! and the byte reads as initialized-but-unknown instead of as a read of
//! uninitialized storage.
//!
//! Entries are keyed by the pointer that starts them and carry a byte length.
//! Constant-offset entries of one block are *runs*: disjoint, non-adjacent
//! intervals, merged as they are recorded, so a fully written array is one
//! entry however many element stores wrote it, and a covering query is one
//! predecessor lookup. A symbolic-offset entry is an exact spelling with the
//! widest access recorded at it; it covers only a read at that spelling.
//!
//! Every operation touches the entries of the one block it names (O(log n)
//! to position plus the entries it merges or visits), never unrelated blocks.

use super::{Address, AddressBase, AliasCandidates, HashedOrdMap, OldAddressOffset, ProgramValue};

/// See the module comment.
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct InitializedBytes {
    /// Start pointer to byte length. Invariant: within one block, the
    /// constant-offset entries are pairwise disjoint and non-adjacent, and
    /// every length is nonzero.
    entries: HashedOrdMap<Address, u32>,
    /// Exact addresses of partially initialized bytes. Zero and full masks
    /// never occupy this index.
    partial: HashedOrdMap<Address, PartialByte>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct PartialByte {
    pub(crate) mask: u8,
    pub(crate) value: Option<ProgramValue>,
}

impl std::hash::Hash for InitializedBytes {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.entries.hash(state);
        if !self.partial.is_empty() {
            self.partial.hash(state);
        }
    }
}

fn constant_start(block: &AddressBase, offset: i64) -> Address {
    Address {
        base: block.clone(),
        offset: OldAddressOffset::Constant(offset),
    }
}

impl InitializedBytes {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// The entries as a state map, for the generic observable-entry and
    /// relative-equality comparisons.
    pub(crate) fn as_map(&self) -> &HashedOrdMap<Address, u32> {
        &self.entries
    }

    /// The address index for sub-byte initialization metadata.
    pub(crate) fn partial_map(&self) -> &HashedOrdMap<Address, PartialByte> {
        &self.partial
    }

    /// Equality of two records derived from `base`; see
    /// [`HashedOrdMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.entries.eq_relative_to(&other.entries, &base.entries)
            && self.partial.eq_relative_to(&other.partial, &base.partial)
    }

    /// The run of constant offsets in `block` that starts at or before
    /// `offset`, nearest first: the only run that can contain it.
    fn run_at_or_before(&self, block: &AddressBase, offset: i64) -> Option<(i64, i64)> {
        self.entries
            .range(constant_start(block, i64::MIN)..=constant_start(block, offset))
            .next_back()
            .and_then(|(start, length)| {
                let start = start.offset.as_const()?;
                Some((start, start + i64::from(*length)))
            })
    }

    /// Whether every one of the `byte_width` bytes at `pointer` is recorded
    /// as initialized.
    pub(crate) fn covers(&self, pointer: &Address, byte_width: u32) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        match pointer.offset.as_const() {
            Some(offset) => self
                .run_at_or_before(&pointer.base, offset)
                .is_some_and(|(_, end)| end >= offset + i64::from(byte_width)),
            None => self
                .entries
                .get(pointer)
                .is_some_and(|length| *length >= byte_width),
        }
    }

    /// Guaranteed initialized bits at the selected byte's exact address.
    pub(crate) fn mask_at(&self, address: &Address) -> u8 {
        if self.covers(address, 1) {
            u8::MAX
        } else {
            self.partial_byte(address).map_or(0, |byte| byte.mask)
        }
    }

    pub(crate) fn partial_byte(&self, address: &Address) -> Option<&PartialByte> {
        crate::instrumentation::record_deterministic_work(1);
        self.partial.get(address)
    }

    /// Record initialization of selected bits, promoting a completed byte
    /// to the interval index also used by normal byte loads.
    #[cfg(test)]
    pub(crate) fn record_mask(&mut self, address: &Address, mask: u8) -> bool {
        let before = self.mask_at(address);
        let combined = before | mask;
        if before == combined {
            return false;
        }
        if combined == u8::MAX {
            return self.record(address, 1);
        }
        self.set_partial(address.clone(), combined, None);
        true
    }

    pub(crate) fn set_partial(&mut self, address: Address, mask: u8, value: Option<ProgramValue>) {
        debug_assert!(mask != 0 && mask != u8::MAX);
        debug_assert!(
            value
                .as_ref()
                .is_none_or(|value| matches!(value, ProgramValue::UInt8(_)))
        );
        self.partial.insert(address, PartialByte { mask, value });
    }

    pub(crate) fn partial_in_range(
        &self,
        block: &AddressBase,
        start: i64,
        end: i64,
    ) -> impl Iterator<Item = (&Address, &PartialByte)> {
        crate::instrumentation::record_deterministic_work(1);
        self.partial
            .range(constant_start(block, start)..constant_start(block, end))
    }

    pub(crate) fn forget_partial_values(
        &mut self,
        candidates: Option<(&AliasCandidates, &[(Address, Address)])>,
        mut keep: impl FnMut(&Address, &ProgramValue) -> bool,
    ) -> bool {
        let mut forget = |(address, byte): (&Address, &PartialByte)| {
            crate::instrumentation::record_deterministic_work(1);
            let value = byte.value.as_ref()?;
            (!keep(address, value)).then(|| (address.clone(), byte.mask))
        };
        let dropped: Vec<_> = match candidates {
            Some((candidates, kept)) if !kept.is_empty() => {
                let (entries, visited) = candidates.entries_outside(&self.partial, kept);
                crate::instrumentation::record_deterministic_work(visited);
                entries.into_iter().filter_map(&mut forget).collect()
            }
            Some((candidates, _)) => candidates
                .entries(&self.partial)
                .filter_map(&mut forget)
                .collect(),
            None => self.partial.iter().filter_map(&mut forget).collect(),
        };
        for (address, mask) in &dropped {
            self.set_partial(address.clone(), *mask, None);
        }
        !dropped.is_empty()
    }

    /// Remove just the exact partial-byte entries covered by this access.
    pub(super) fn forget_masks(&mut self, address: &Address, width: u32) -> bool {
        if self.partial.is_empty() || width == 0 {
            return false;
        }
        let Some(start) = address.offset.as_const() else {
            return self.partial.remove(address).is_some();
        };
        let end = start + i64::from(width);
        let selected = self
            .partial
            .range(constant_start(&address.base, start)..constant_start(&address.base, end))
            .map(|(address, _)| address.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(selected.len() + 1);
        for address in &selected {
            self.partial.remove(address);
        }
        !selected.is_empty()
    }

    /// The end of the run of `block` holding the byte at `offset`, if one
    /// does: one predecessor lookup.
    pub(crate) fn run_end_holding(&self, block: &AddressBase, offset: i64) -> Option<i64> {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, offset)
            .map(|(_, end)| end)
            .filter(|end| *end > offset)
    }

    /// Whether one run of `block` holds every byte in `start..end`.
    pub(crate) fn covers_interval(&self, block: &AddressBase, start: i64, end: i64) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, start)
            .is_some_and(|(_, run_end)| run_end >= end)
    }

    /// The constant-offset runs of `block`, ascending, as start and length.
    pub(crate) fn constant_runs_in_block(&self, block: &AddressBase) -> Vec<(i64, u32)> {
        let runs = AliasCandidates::only_block(block)
            .entries(&self.entries)
            .filter_map(|(start, length)| Some((start.offset.as_const()?, *length)))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(runs.len() + 1);
        runs
    }

    /// Recorded initialization within a concrete byte span, clipped at both
    /// endpoints. A predecessor locates any run straddling the start.
    pub(crate) fn constant_runs_in_range(
        &self,
        block: &AddressBase,
        start: i64,
        end: i64,
    ) -> impl Iterator<Item = (i64, u32)> + '_ {
        let first = self
            .run_at_or_before(block, start)
            .filter(|(_, run_end)| *run_end > start)
            .map_or(start, |(run_start, _)| run_start);
        crate::instrumentation::record_deterministic_work(1);
        self.entries
            .range(constant_start(block, first)..constant_start(block, end))
            .map(move |(address, length)| {
                crate::instrumentation::record_deterministic_work(1);
                let offset = address.offset.as_const().expect("constant offset range");
                let lo = offset.max(start);
                let hi = (offset + i64::from(*length)).min(end);
                (lo, u32::try_from(hi - lo).expect("clipped run"))
            })
    }

    /// Symbolic spellings in a block may designate the destination of a
    /// concrete write. Drop those spellings when replacing initialization;
    /// exact byte runs outside the written span still hold.
    pub(crate) fn forget_symbolic_offsets(&mut self, block: &AddressBase) {
        use std::ops::Bound::{Excluded, Unbounded};
        let addresses = self
            .entries
            .range((Excluded(constant_start(block, i64::MAX)), Unbounded))
            .take_while(|(address, _)| &address.base == block)
            .map(|(address, _)| address.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(addresses.len() + 1);
        for address in addresses {
            self.entries.remove(&address);
        }
    }

    /// Records that the `byte_width` bytes at `pointer` are initialized.
    /// Returns whether the record changed: recording bytes it already covers
    /// leaves it (and so the state's content) exactly as it was.
    pub(crate) fn record(&mut self, pointer: &Address, byte_width: u32) -> bool {
        if byte_width == 0 {
            return false;
        }
        let Some(offset) = pointer.offset.as_const() else {
            if self
                .entries
                .get(pointer)
                .is_some_and(|length| *length >= byte_width)
            {
                return false;
            }
            self.forget_masks(pointer, byte_width);
            self.entries.insert(pointer.clone(), byte_width);
            return true;
        };
        let block = &pointer.base;
        let mut start = offset;
        let mut end = offset + i64::from(byte_width);
        if let Some((before_start, before_end)) = self.run_at_or_before(block, offset)
            && before_end >= start
        {
            if before_end >= end {
                return false;
            }
            start = before_start;
        }
        // Every later run that the new interval reaches or touches merges.
        let merged = self
            .entries
            .range(constant_start(block, start)..=constant_start(block, end))
            .filter_map(|(key, length)| {
                key.offset
                    .as_const()
                    .map(|key_start| (key.clone(), key_start + i64::from(*length)))
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(merged.len() + 1);
        for (key, key_end) in merged {
            end = end.max(key_end);
            self.entries.remove(&key);
        }
        let Ok(length) = u32::try_from(end - start) else {
            // Wider than any object; recording nothing only loses knowledge.
            return false;
        };
        self.forget_masks(pointer, byte_width);
        self.entries.insert(constant_start(block, start), length);
        true
    }

    /// Forgets the `byte_width` bytes at `pointer`: at a constant offset, the
    /// part of every run that holds them, splitting a run that straddles
    /// either end; at a symbolic offset, the entry of that exact spelling.
    /// Returns whether the record changed.
    pub(crate) fn forget(&mut self, pointer: &Address, byte_width: u32) -> bool {
        let forgot_partial = self.forget_masks(pointer, byte_width);
        let Some(start) = pointer.offset.as_const() else {
            return self.entries.remove(pointer).is_some() | forgot_partial;
        };
        if byte_width == 0 {
            return false;
        }
        let block = &pointer.base;
        let end = start + i64::from(byte_width);
        let first = self
            .run_at_or_before(block, start)
            .filter(|(_, run_end)| *run_end > start)
            .map_or(start, |(run_start, _)| run_start);
        let overlapping = self
            .entries
            .range(constant_start(block, first)..constant_start(block, end))
            .filter_map(|(key, length)| {
                let key_start = key.offset.as_const()?;
                let key_end = key_start + i64::from(*length);
                (key_end > start && key_start < end).then_some((key_start, key_end))
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(overlapping.len() + 1);
        if overlapping.is_empty() {
            return forgot_partial;
        }
        for (run_start, run_end) in overlapping {
            self.entries.remove(&constant_start(block, run_start));
            if run_start < start {
                self.entries.insert(
                    constant_start(block, run_start),
                    u32::try_from(start - run_start).expect("a piece of a run"),
                );
            }
            if run_end > end {
                self.entries.insert(
                    constant_start(block, end),
                    u32::try_from(run_end - end).expect("a piece of a run"),
                );
            }
        }
        true
    }

    /// Forgets every entry of `block`: its object's lifetime ended, so a
    /// later object must start uninitialized.
    pub(crate) fn forget_block(&mut self, block: &AddressBase) {
        let candidates = AliasCandidates::only_block(block);
        candidates.retain_map(&mut self.entries, |_, _| false);
        candidates.retain_map(&mut self.partial, |_, _| false);
    }

    /// Removes the candidate entries `keep` rejects, as
    /// [`AliasCandidates::retain_map`]. Removing whole entries keeps the run
    /// invariant.
    pub(crate) fn retain_candidates(
        &mut self,
        candidates: &AliasCandidates,
        mut keep: impl FnMut(&Address, &u32) -> bool,
    ) {
        candidates.retain_map(&mut self.entries, &mut keep);
        candidates.retain_map(&mut self.partial, |address, _| keep(address, &1));
    }

    /// The bytes both records cover. A constant run keeps the parts the other
    /// record's runs cover; a symbolic spelling needs the same spelling in
    /// both, at the narrower width. The result keeps the run invariant: two
    /// clipped pieces are separated by a gap of one side or the other.
    pub(crate) fn intersection(&self, other: &Self) -> Self {
        // Shared partial entries stay unchanged. For each changed address
        // either side may instead cover it with a complete byte run.
        let mut partial = self.partial.clone();
        for change in self.partial.diff(&other.partial) {
            let address = change.key();
            let mask = self.mask_at(address) & other.mask_at(address);
            if mask == 0 {
                partial.remove(address);
            } else {
                partial.insert(address.clone(), PartialByte { mask, value: None });
            }
        }
        // Equal byte runs intersect to themselves.
        if self.entries.ptr_eq(&other.entries) || self.entries == other.entries {
            return Self {
                entries: self.entries.clone(),
                partial,
            };
        }
        let mut result = HashedOrdMap::new();
        let mut visited = 0usize;
        for (pointer, length) in self.entries.iter() {
            visited += 1;
            let Some(start) = pointer.offset.as_const() else {
                if let Some(other_length) = other.entries.get(pointer) {
                    result.insert(pointer.clone(), (*length).min(*other_length));
                }
                continue;
            };
            let end = start + i64::from(*length);
            let first = other
                .run_at_or_before(&pointer.base, start)
                .map_or(start, |(other_start, _)| other_start);
            for (other_pointer, other_length) in other
                .entries
                .range(constant_start(&pointer.base, first)..constant_start(&pointer.base, end))
            {
                visited += 1;
                let Some(other_start) = other_pointer.offset.as_const() else {
                    continue;
                };
                let other_end = other_start + i64::from(*other_length);
                let piece_start = start.max(other_start);
                let piece_end = end.min(other_end);
                if piece_start < piece_end {
                    result.insert(
                        constant_start(&pointer.base, piece_start),
                        u32::try_from(piece_end - piece_start).expect("a piece of a run"),
                    );
                }
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        Self {
            entries: result,
            partial,
        }
    }

    /// Replace the destination range's known initialization with the
    /// source snapshot's. The byte-copy caller supplies checked bounds and
    /// accounts for any initialization implicit in the source's authority.
    /// Only exact constant offsets can be translated here.
    pub(crate) fn copy_exact_range_from(
        &mut self,
        source: &Self,
        from: &Address,
        to: &Address,
        width: u32,
    ) -> Option<()> {
        let from_start = from.offset.as_const()?;
        let to_start = to.offset.as_const()?;
        let from_end = from_start.checked_add(i64::from(width))?;
        to_start.checked_add(i64::from(width))?;
        if width == 0 {
            return Some(());
        }
        let destination = |offset| constant_start(&to.base, to_start + (offset - from_start));
        self.forget(to, width);
        for (start, bytes) in source.constant_runs_in_range(&from.base, from_start, from_end) {
            self.record(&destination(start), bytes);
        }
        for (address, byte) in source.partial_in_range(&from.base, from_start, from_end) {
            crate::instrumentation::record_deterministic_work(1);
            let start = address.offset.as_const().expect("constant offset range");
            self.set_partial(destination(start), byte.mask, byte.value.clone());
        }
        Some(())
    }

    /// The same record with every start pointer rewritten, re-merged so the
    /// run invariant holds even where the rewrite made a symbolic start
    /// constant.
    pub(crate) fn map_pointers(
        &self,
        mut rewrite: impl FnMut(&Address) -> Address,
        mut rewrite_value: impl FnMut(&ProgramValue) -> ProgramValue,
    ) -> Self {
        let mut result = Self::default();
        for (pointer, length) in self.entries.iter() {
            result.record(&rewrite(pointer), *length);
        }
        for (address, byte) in self.partial.iter() {
            let address = rewrite(address);
            if !result.covers(&address, 1) {
                result.set_partial(
                    address,
                    byte.mask,
                    byte.value.as_ref().map(&mut rewrite_value),
                );
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(block: &str, offset: i64) -> Address {
        constant_start(&AddressBase::from(block), offset)
    }

    #[test]
    fn partial_writes_promote_only_a_completed_byte() {
        let mut record = InitializedBytes::default();
        let address = at("local:flags", 0);
        assert!(record.record_mask(&address, 1));
        assert_eq!(record.mask_at(&address), 1);
        assert!(!record.covers(&address, 1));
        assert!(record.record_mask(&address, 2));
        assert_eq!(record.mask_at(&address), 3);
        assert!(!record.record_mask(&address, 2));
        assert!(record.record_mask(&address, 252));
        assert!(record.covers(&address, 1));
        assert!(record.partial_map().is_empty());
    }

    #[test]
    fn partial_initialization_survives_only_guaranteed_bits_of_a_join() {
        let mut left = InitializedBytes::default();
        let first = at("local:flags", 0);
        let second = at("local:flags", 1);
        left.record_mask(&first, 3);
        left.record_mask(&second, 1);
        let mut right = left.clone();
        right.record(&first, 1);
        right.record_mask(&second, 4);
        let mut joined = left.intersection(&right);
        assert_eq!(joined.mask_at(&first), 3);
        assert_eq!(joined.mask_at(&second), 1);
        assert_eq!(joined, right.intersection(&left));
        assert!(joined.forget(&first, 1));
        assert_eq!(joined.mask_at(&first), 0);
        assert_eq!(joined.mask_at(&second), 1);
        joined.forget_block(&second.base);
        assert_eq!(joined, InitializedBytes::default());
    }

    #[test]
    fn ordinary_memory_store_and_lifetime_use_the_same_initialization_record() {
        use crate::kernel::{SymbolicMemory, uint8};
        let address = at("local:flags", 0);
        let mut partial = SymbolicMemory::new().with_uninitialized_block(address.base.clone(), 1);
        std::sync::Arc::make_mut(&mut partial.heap)
            .initialized
            .record_mask(&address, 1);
        assert!(!partial.has_initialized_bytes_at(&address, 1));
        let written = partial.clone().store(address.clone(), uint8(3));
        assert!(written.has_initialized_bytes_at(&address, 1));
        assert!(written.heap.initialized.partial_map().is_empty());
        let ended = partial.without_local_block(&address.base);
        assert_eq!(ended.heap.initialized.mask_at(&address), 0);
    }

    #[test]
    fn copying_replaces_destination_initialization_including_unwritten_bits() {
        let from = at("local:source", 1);
        let to = at("local:dest", 2);
        let mut state = InitializedBytes::default();
        state.record(&at("local:source", 0), 2);
        state.record_mask(&at("local:source", 2), 3);
        state.record(&at("local:dest", 0), 6);
        let source_snapshot = state.clone();
        state
            .copy_exact_range_from(&source_snapshot, &from, &to, 3)
            .unwrap();
        assert_eq!(state.mask_at(&at("local:dest", 1)), u8::MAX);
        assert_eq!(state.mask_at(&to), u8::MAX);
        assert_eq!(state.mask_at(&at("local:dest", 3)), 3);
        assert_eq!(state.mask_at(&at("local:dest", 4)), 0);
        assert_eq!(state.mask_at(&at("local:dest", 5)), u8::MAX);
        assert_eq!(state.mask_at(&at("local:source", 2)), 3);
    }

    #[test]
    fn element_stores_merge_into_one_run() {
        let mut record = InitializedBytes::default();
        assert!(record.record(&at("local:a", 4), 4));
        assert!(record.record(&at("local:a", 0), 4));
        assert!(record.record(&at("local:a", 12), 4));
        assert_eq!(record.len(), 2);
        assert!(!record.covers(&at("local:a", 8), 4));
        assert!(record.record(&at("local:a", 8), 4));
        assert_eq!(record.len(), 1);
        assert!(record.covers(&at("local:a", 0), 16));
        assert!(!record.covers(&at("local:a", 0), 17));
        assert!(!record.record(&at("local:a", 6), 1));
        // Another block is untouched by the merge and uncovered.
        assert!(!record.covers(&at("local:b", 0), 1));
    }

    #[test]
    fn a_partial_record_does_not_cover_its_neighbour() {
        let mut record = InitializedBytes::default();
        record.record(&at("local:a", 0), 4);
        assert!(!record.covers(&at("local:a", 2), 4));
        assert!(record.covers(&at("local:a", 2), 2));
        assert!(!record.covers(&at("local:a", 4), 4));
    }

    #[test]
    fn forgetting_splits_the_run_that_holds_the_bytes() {
        let mut record = InitializedBytes::default();
        record.record(&at("local:a", 0), 16);
        assert!(record.forget(&at("local:a", 4), 4));
        assert_eq!(record.len(), 2);
        assert!(record.covers(&at("local:a", 0), 4));
        assert!(!record.covers(&at("local:a", 4), 1));
        assert!(record.covers(&at("local:a", 8), 8));
        assert!(!record.forget(&at("local:a", 4), 4));
        assert!(record.forget(&at("local:a", 2), 8));
        assert!(record.covers(&at("local:a", 0), 2));
        assert!(!record.covers(&at("local:a", 2), 1));
        assert!(record.covers(&at("local:a", 10), 6));
    }

    #[test]
    fn intersection_keeps_the_bytes_both_sides_cover() {
        let mut left = InitializedBytes::default();
        left.record(&at("local:a", 0), 16);
        let mut right = InitializedBytes::default();
        right.record(&at("local:a", 4), 4);
        right.record(&at("local:a", 12), 8);
        right.record(&at("local:b", 0), 4);
        let both = left.intersection(&right);
        assert_eq!(both.len(), 2);
        assert!(both.covers(&at("local:a", 4), 4));
        assert!(both.covers(&at("local:a", 12), 4));
        assert!(!both.covers(&at("local:a", 0), 4));
        assert!(!both.covers(&at("local:a", 16), 4));
        assert!(!both.covers(&at("local:b", 0), 4));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/initialized_bytes/tests.rs");
    }
}
