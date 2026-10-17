//! The effective types of heap cells (C11 6.5p6), for the strict-aliasing
//! check (`design/effective-types.md`).
//!
//! Heap storage has no declared type: a C store gives the cell it writes the
//! type of the lvalue it writes through, and a later access must be allowed
//! for that type. Each entry records the cell's class beside the value the
//! store wrote, and counts only while the cell still holds that value. Any
//! other change to the cell (a store this record does not see, a call or
//! loop havoc, a join, a free) leaves the entry unconfirmed, and an
//! unconfirmed entry is ignored: the access falls back to what is known
//! without it. So no other memory operation has to maintain the record.
//!
//! Entries are kept only for constant offsets of heap blocks, whose
//! addresses mention no variable. Every operation touches the entries of the
//! one block it names, positioned in O(log n).

use super::{CValue, Pointer, PointerBlock, PointerOffsetTerm, SnapshotMap};
use crate::kernel::effective_type::CAccessClass;

/// The widest scalar a store writes, which bounds how far before a store an
/// entry it overlaps can start.
const MAX_CELL_WIDTH: i64 = 16;

/// See the module comment.
#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct HeapEffectiveTypes {
    /// Cell start to its width, class and the value the store wrote.
    /// Invariant: within one block, entries are pairwise disjoint.
    entries: SnapshotMap<Pointer, HeapEffectiveType>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct HeapEffectiveType {
    width: u32,
    class: CAccessClass,
    value: CValue,
}

fn constant_start(block: &PointerBlock, offset: i64) -> Pointer {
    Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

impl HeapEffectiveTypes {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Equality of two records derived from `base`; see
    /// [`SnapshotMap::eq_relative_to`].
    pub(crate) fn eq_relative_to(&self, other: &Self, base: &Self) -> bool {
        self.entries.eq_relative_to(&other.entries, &base.entries)
    }

    /// Records that a C store of `value`, `width` bytes wide, wrote the cell
    /// at `pointer` through an lvalue of `class`. Entries the store overlaps
    /// are dropped; a store with no class, as a character store, records
    /// none. A store at a symbolic offset may overwrite any cell of its
    /// block, so it drops the whole block's entries. Returns whether the
    /// record changed.
    pub(crate) fn record(
        &mut self,
        pointer: &Pointer,
        width: u32,
        class: Option<CAccessClass>,
        value: &CValue,
    ) -> bool {
        if !matches!(pointer.block, PointerBlock::Heap(_)) {
            return false;
        }
        let block = &pointer.block;
        let Some(offset) = pointer.offset.as_const() else {
            return self.forget_block(block);
        };
        let end = offset + i64::from(width);
        let overlapping = self
            .entries
            .range(
                constant_start(block, offset.saturating_sub(MAX_CELL_WIDTH - 1))
                    ..constant_start(block, end),
            )
            .filter_map(|(key, entry)| {
                let start = key.offset.as_const()?;
                (start + i64::from(entry.width) > offset).then(|| key.clone())
            })
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(overlapping.len() + 1);
        let mut changed = false;
        for key in overlapping {
            changed |= self.entries.remove(&key).is_some();
        }
        if let Some(class) = class {
            let entry = HeapEffectiveType {
                width,
                class,
                value: value.clone(),
            };
            changed |= self.entries.insert(pointer.clone(), entry.clone()) != Some(entry);
        }
        changed
    }

    /// The record with every stored value rewritten by `rewrite`, as a
    /// substitution rewrites the cells, so each entry stays confirmable.
    pub(crate) fn map_values(&self, mut rewrite: impl FnMut(&CValue) -> CValue) -> Self {
        crate::instrumentation::record_deterministic_work(self.entries.len() + 1);
        Self {
            entries: self
                .entries
                .iter()
                .map(|(pointer, entry)| {
                    (
                        pointer.clone(),
                        HeapEffectiveType {
                            value: rewrite(&entry.value),
                            ..entry.clone()
                        },
                    )
                })
                .collect(),
        }
    }

    /// Drops every entry of `block`. Returns whether the record changed.
    pub(crate) fn forget_block(&mut self, block: &PointerBlock) -> bool {
        let keys = self
            .entries
            .range(constant_start(block, i64::MIN)..=constant_start(block, i64::MAX))
            .map(|(key, _)| key.clone())
            .collect::<Vec<_>>();
        crate::instrumentation::record_deterministic_work(keys.len() + 1);
        for key in &keys {
            self.entries.remove(key);
        }
        !keys.is_empty()
    }

    /// The effective class of the cell starting at `pointer`, when a store
    /// recorded one and the cell still holds the value it wrote, as
    /// `current` says.
    pub(crate) fn class_at(
        &self,
        pointer: &Pointer,
        current: Option<&CValue>,
    ) -> Option<CAccessClass> {
        crate::instrumentation::record_deterministic_work(1);
        let entry = self.entries.get(pointer)?;
        (current == Some(&entry.value)).then(|| entry.class.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::effective_type::CScalarClass;

    fn cell(offset: i64) -> Pointer {
        constant_start(&PointerBlock::Heap(7), offset)
    }

    fn int(value: u32) -> CValue {
        CValue::Int32(super::super::Bitvector32Term::Constant(value))
    }

    const INT: CAccessClass = CAccessClass::Scalar(CScalarClass::Int);
    const LONG: CAccessClass = CAccessClass::Scalar(CScalarClass::Long);

    #[test]
    fn an_entry_counts_while_its_cell_holds_the_stored_value() {
        let mut record = HeapEffectiveTypes::default();
        record.record(&cell(0), 4, Some(INT), &int(1));
        assert_eq!(record.class_at(&cell(0), Some(&int(1))), Some(INT));
        assert_eq!(record.class_at(&cell(0), Some(&int(2))), None);
        assert_eq!(record.class_at(&cell(0), None), None);
    }

    #[test]
    fn a_store_replaces_the_entries_it_overlaps() {
        let mut record = HeapEffectiveTypes::default();
        record.record(&cell(0), 4, Some(INT), &int(1));
        record.record(&cell(4), 4, Some(INT), &int(2));
        record.record(&cell(0), 8, Some(LONG), &int(3));
        assert_eq!(record.len(), 1);
        assert_eq!(record.class_at(&cell(0), Some(&int(3))), Some(LONG));
        // A character store records nothing but still drops what it wrote.
        record.record(&cell(2), 1, None, &int(4));
        assert_eq!(record.len(), 0);
    }

    #[test]
    fn a_symbolic_store_drops_its_block_only() {
        let mut record = HeapEffectiveTypes::default();
        record.record(&cell(0), 4, Some(INT), &int(1));
        let other = constant_start(&PointerBlock::Heap(8), 0);
        record.record(&other, 4, Some(INT), &int(1));
        let symbolic = Pointer {
            block: PointerBlock::Heap(7),
            offset: PointerOffsetTerm::scale_int32(
                super::super::Bitvector32Term::Variable(super::super::Variable(1)),
                4,
            ),
        };
        record.record(&symbolic, 4, Some(INT), &int(1));
        assert_eq!(record.len(), 1);
        assert_eq!(record.class_at(&other, Some(&int(1))), Some(INT));
    }
}
