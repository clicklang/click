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
//! predecessor lookup. Symbolic offsets use the same runs within each common
//! offset stem, indexed by their checked constant displacements. A covering
//! query visits only its own family with one predecessor lookup.
//!
//! Every operation touches the entries of the one block it names (O(log n)
//! to position plus the entries it merges or visits), never unrelated blocks.

use super::{AliasCandidates, Pointer, PointerBlock, PointerOffsetTerm, SnapshotMap};

/// See the module comment.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct InitializedBytes {
    /// Start pointer to byte length. Within each block/offset family, runs
    /// are pairwise disjoint and non-adjacent; every length is nonzero.
    entries: SnapshotMap<Pointer, u32>,
}

#[cfg(test)]
fn constant_start(block: &PointerBlock, offset: i64) -> Pointer {
    Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

// A canonical offset family and a checked constant displacement. Do not
// saturate: that could identify different addresses as the same initialized byte.
fn offset_family(offset: &PointerOffsetTerm) -> Option<(Option<&PointerOffsetTerm>, i64)> {
    if let Some(constant) = offset.as_const() {
        return Some((None, constant));
    }
    let mut stem = offset;
    let mut shift = 0i64;
    while let PointerOffsetTerm::Add(left, right) = stem {
        let Some(constant) = right.as_const() else {
            break;
        };
        shift = shift.checked_add(constant)?;
        stem = left;
    }
    if let Some(constant) = stem.as_const() {
        Some((None, shift.checked_add(constant)?))
    } else {
        Some((Some(stem), shift))
    }
}

fn family_start(block: &PointerBlock, stem: Option<&PointerOffsetTerm>, offset: i64) -> Pointer {
    Pointer {
        block: block.clone(),
        offset: match stem {
            None => PointerOffsetTerm::Constant(offset),
            // Retain the zero displacement too, so all keys in a symbolic family
            // occupy one contiguous ordered range. These are private record keys.
            Some(stem) => PointerOffsetTerm::Add(
                Box::new(stem.clone()),
                Box::new(PointerOffsetTerm::Constant(offset)),
            ),
        },
    }
}

impl InitializedBytes {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// The entries as a snapshot map, for the generic observable-entry and
    /// relative-equality comparisons.
    pub(crate) fn as_map(&self) -> &SnapshotMap<Pointer, u32> {
        &self.entries
    }

    /// Equality of two records derived from `base`; see
    /// [`SnapshotMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.entries.eq_relative_to(&other.entries, &base.entries)
    }

    fn family_run_at_or_before(
        &self,
        block: &PointerBlock,
        stem: Option<&PointerOffsetTerm>,
        offset: i64,
    ) -> Option<(i64, i64)> {
        self.entries
            .range(family_start(block, stem, i64::MIN)..=family_start(block, stem, offset))
            .next_back()
            .and_then(|(pointer, length)| {
                let (_, start) = offset_family(&pointer.offset)?;
                Some((start, start.checked_add(i64::from(*length))?))
            })
    }

    fn run_at_or_before(&self, block: &PointerBlock, offset: i64) -> Option<(i64, i64)> {
        self.family_run_at_or_before(block, None, offset)
    }

    /// Whether every one of the `byte_width` bytes at `pointer` is recorded
    /// as initialized.
    pub(crate) fn covers(&self, pointer: &Pointer, byte_width: u32) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        let Some((stem, start)) = offset_family(&pointer.offset) else {
            return false;
        };
        let Some(end) = start.checked_add(i64::from(byte_width)) else {
            return false;
        };
        self.family_run_at_or_before(&pointer.block, stem, start)
            .is_some_and(|(_, run_end)| run_end >= end)
    }

    /// The end of the run of `block` holding the byte at `offset`, if one
    /// does: one predecessor lookup.
    pub(crate) fn run_end_holding(&self, block: &PointerBlock, offset: i64) -> Option<i64> {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, offset)
            .map(|(_, end)| end)
            .filter(|end| *end > offset)
    }

    /// Whether one run of `block` holds every byte in `start..end`.
    pub(crate) fn covers_interval(&self, block: &PointerBlock, start: i64, end: i64) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.run_at_or_before(block, start)
            .is_some_and(|(_, run_end)| run_end >= end)
    }

    /// The constant-offset runs of `block`, ascending, as start and length.
    pub(crate) fn constant_runs_in_block(&self, block: &PointerBlock) -> Vec<(i64, u32)> {
        let runs = AliasCandidates::only_block(block)
            .entries(&self.entries)
            .filter_map(|(start, length)| Some((start.offset.as_const()?, *length)))
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(runs.len() + 1);
        runs
    }

    /// Records that the `byte_width` bytes at `pointer` are initialized.
    /// Returns whether the record changed: recording bytes it already covers
    /// leaves it (and so the snapshot's content) exactly as it was.
    pub(crate) fn record(&mut self, pointer: &Pointer, byte_width: u32) -> bool {
        if byte_width == 0 {
            return false;
        }
        let Some((stem, offset)) = offset_family(&pointer.offset) else {
            return false;
        };
        let block = &pointer.block;
        let mut start = offset;
        let Some(mut end) = offset.checked_add(i64::from(byte_width)) else {
            return false;
        };
        if let Some((before_start, before_end)) = self.family_run_at_or_before(block, stem, offset)
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
            .range(family_start(block, stem, start)..=family_start(block, stem, end))
            .filter_map(|(key, length)| {
                let (_, key_start) = offset_family(&key.offset)?;
                Some((key.clone(), key_start.checked_add(i64::from(*length))?))
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
        self.entries
            .insert(family_start(block, stem, start), length);
        true
    }

    /// Forgets only the overlapping bytes in this offset family, splitting
    /// a run that straddles either end. Other ranges, stems and blocks are
    /// untouched.
    /// Returns whether the record changed.
    pub(crate) fn forget(&mut self, pointer: &Pointer, byte_width: u32) -> bool {
        let Some((stem, start)) = offset_family(&pointer.offset) else {
            return false;
        };
        if byte_width == 0 {
            return false;
        }
        let block = &pointer.block;
        let Some(end) = start.checked_add(i64::from(byte_width)) else {
            return false;
        };
        let first = self
            .family_run_at_or_before(block, stem, start)
            .filter(|(_, run_end)| *run_end > start)
            .map_or(start, |(run_start, _)| run_start);
        let overlapping = self
            .entries
            .range(family_start(block, stem, first)..family_start(block, stem, end))
            .filter_map(|(key, length)| {
                let (_, key_start) = offset_family(&key.offset)?;
                let key_end = key_start.checked_add(i64::from(*length))?;
                (key_end > start && key_start < end).then_some((key_start, key_end))
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(overlapping.len() + 1);
        if overlapping.is_empty() {
            return false;
        }
        for (run_start, run_end) in overlapping {
            self.entries.remove(&family_start(block, stem, run_start));
            if run_start < start {
                self.entries.insert(
                    family_start(block, stem, run_start),
                    u32::try_from(start - run_start).expect("a piece of a run"),
                );
            }
            if run_end > end {
                self.entries.insert(
                    family_start(block, stem, end),
                    u32::try_from(run_end - end).expect("a piece of a run"),
                );
            }
        }
        true
    }

    /// Forgets every entry of `block`: its object's lifetime ended, so a
    /// later object must start uninitialized.
    pub(crate) fn forget_block(&mut self, block: &PointerBlock) {
        AliasCandidates::only_block(block).retain_map(&mut self.entries, |_, _| false);
    }

    /// Removes the candidate entries `keep` rejects, as
    /// [`AliasCandidates::retain_map`]. Removing whole entries keeps the run
    /// invariant.
    pub(crate) fn retain_candidates(
        &mut self,
        candidates: &AliasCandidates,
        keep: impl FnMut(&Pointer, &u32) -> bool,
    ) {
        candidates.retain_map(&mut self.entries, keep);
    }

    /// The bytes both records cover. Each run keeps the parts the other
    /// record's runs in the same offset family cover. The result keeps the
    /// run invariant: two
    /// clipped pieces are separated by a gap of one side or the other.
    pub(crate) fn intersection(&self, other: &Self) -> Self {
        // Equal records intersect to themselves. Two records derived from
        // one are compared along the paths that changed.
        if self.entries.ptr_eq(&other.entries) || self.entries == other.entries {
            return self.clone();
        }
        let mut result = SnapshotMap::new();
        let mut visited = 0usize;
        for (pointer, length) in self.entries.iter() {
            visited += 1;
            let Some((stem, start)) = offset_family(&pointer.offset) else {
                continue;
            };
            let end = start + i64::from(*length);
            let first = other
                .family_run_at_or_before(&pointer.block, stem, start)
                .map_or(start, |(other_start, _)| other_start);
            for (other_pointer, other_length) in other.entries.range(
                family_start(&pointer.block, stem, first)..family_start(&pointer.block, stem, end),
            ) {
                visited += 1;
                let Some((_, other_start)) = offset_family(&other_pointer.offset) else {
                    continue;
                };
                let other_end = other_start + i64::from(*other_length);
                let piece_start = start.max(other_start);
                let piece_end = end.min(other_end);
                if piece_start < piece_end {
                    result.insert(
                        family_start(&pointer.block, stem, piece_start),
                        u32::try_from(piece_end - piece_start).expect("a piece of a run"),
                    );
                }
            }
        }
        crate::instrumentation::record_deterministic_work(visited);
        Self { entries: result }
    }

    /// The same record with every start pointer rewritten, re-merged so the
    /// run invariant holds even where the rewrite made a symbolic start
    /// constant.
    pub(crate) fn map_pointers(&self, mut rewrite: impl FnMut(&Pointer) -> Pointer) -> Self {
        let mut result = Self::default();
        for (pointer, length) in self.entries.iter() {
            result.record(&rewrite(pointer), *length);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(block: &str, offset: i64) -> Pointer {
        constant_start(&PointerBlock::from(block), offset)
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

    #[test]
    fn symbolic_coverage_follows_whole_writes_and_refuses_gaps() {
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(super::super::Variable(7410)),
        };
        let mut record = InitializedBytes::default();
        record.record(&base, 2);
        record.record(&base.offset_by_bytes(3), 1);
        assert!(!record.covers(&base, 4));
        record.record(&base.offset_by_bytes(2), 1);
        assert!(record.covers(&base, 4));
        assert!(!record.covers(&base, 5));
        assert!(record.covers(&base.offset_by_bytes(1), 3));
        let mut wide = InitializedBytes::default();
        wide.record(&base, 4);
        assert!(wide.covers(&base.offset_by_bytes(1), 3));
        assert!(!wide.covers(&base.offset_by_bytes(1), 4));
        wide.forget(&base.offset_by_bytes(1), 1);
        assert!(wide.covers(&base, 1));
        assert!(!wide.covers(&base.offset_by_bytes(1), 1));
        let mut large = InitializedBytes::default();
        large.record(&base, u32::MAX);
        let (holds, work) =
            crate::instrumentation::measure_deterministic_work(|| large.covers(&base, u32::MAX));
        assert!(holds);
        assert_eq!(work, 1, "one recorded run must take one lookup");
        let overflow = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Add(
                    Box::new(base.offset.clone()),
                    Box::new(PointerOffsetTerm::Constant(i64::MAX)),
                )),
                Box::new(PointerOffsetTerm::Constant(1)),
            ),
        };
        let mut invalid = InitializedBytes::default();
        invalid.record(&overflow, 4);
        assert!(
            !invalid.covers(&overflow, 4),
            "displacements must not saturate into initialization authority"
        );
        record.forget_block(&base.block);
        assert!(!record.covers(&base, 4));
    }

    #[test]
    fn symbolic_coverage_does_not_visit_unrelated_same_block_writes() {
        let mut samples = Vec::new();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(super::super::Variable(7411)),
        };
        for count in [8, 32, 128, 512] {
            let mut record = InitializedBytes::default();
            for index in 0..4 {
                record.record(&base.offset_by_bytes(index), 1);
            }
            for index in 0..count {
                record.record(&base.offset_by_bytes(index + 100), 1);
                record.record(&at(&format!("local:other{index}"), 0), 4);
            }
            let (holds, work) =
                crate::instrumentation::measure_deterministic_work(|| record.covers(&base, 4));
            assert!(holds);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }

    #[test]
    fn symbolic_run_intersection_and_rewriting_preserve_the_common_bytes() {
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(super::super::Variable(7420)),
        };
        let mut whole = InitializedBytes::default();
        whole.record(&base, 8);
        let mut pieces = InitializedBytes::default();
        for index in 0..4 {
            pieces.record(&base.offset_by_bytes(index), 1);
        }
        pieces.record(&base.offset_by_bytes(6), 4);
        let common = whole.intersection(&pieces);
        assert!(common.covers(&base, 4));
        assert!(!common.covers(&base.offset_by_bytes(4), 1));
        assert!(common.covers(&base.offset_by_bytes(6), 2));
        assert!(!common.covers(&base.offset_by_bytes(8), 1));
        assert_eq!(common, pieces.intersection(&whole));
        let rewritten = common.map_pointers(|pointer| {
            let (_, shift) = offset_family(&pointer.offset).unwrap();
            at("local:rewritten", shift + 8)
        });
        assert!(rewritten.covers(&at("local:rewritten", 8), 4));
        assert!(!rewritten.covers(&at("local:rewritten", 12), 1));
        assert!(rewritten.covers(&at("local:rewritten", 14), 2));
    }

    #[test]
    fn symbolic_run_reset_touches_only_overlapping_runs() {
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(super::super::Variable(7421)),
        };
        let mut samples = Vec::new();
        for count in [8, 32, 128, 512] {
            let mut record = InitializedBytes::default();
            record.record(&base, 4);
            for index in 0..count {
                record.record(&base.offset_by_bytes(100 + 2 * index), 1);
                record.record(
                    &Pointer {
                        block: base.block.clone(),
                        offset: PointerOffsetTerm::Variable(super::super::Variable(
                            7500 + u64::from(index),
                        )),
                    },
                    4,
                );
            }
            let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
                record.forget(&base.offset_by_bytes(1), 1)
            });
            assert!(changed);
            assert!(record.covers(&base, 1));
            assert!(!record.covers(&base.offset_by_bytes(1), 1));
            assert!(record.covers(&base.offset_by_bytes(2), 2));
            assert!(record.covers(&base.offset_by_bytes(100), 1));
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }

    #[test]
    fn recording_scales_with_the_merged_runs_not_the_record() {
        // Each store into a fresh block, then one store per element of one
        // array: the work per record is the few runs it merges, whatever
        // size the record has reached.
        for size in [64i64, 512, 4096] {
            let mut record = InitializedBytes::default();
            for block in 0..size {
                record.record(&at(&format!("local:other{block}"), 0), 4);
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for element in 0..size {
                    record.record(&at("local:array", element * 4), 4);
                }
            });
            assert!(record.covers(&at("local:array", 0), u32::try_from(size * 4).unwrap()));
            assert!(
                work <= 4 * usize::try_from(size).unwrap(),
                "recording {size} elements cost {work} work units"
            );
        }
    }
}
