//! Planning-only inspection of the cells one checked statement step forgot.
//!
//! A scalar store keeps a cached cell of the written array only on direct
//! evidence that the two element indices differ
//! (`reasoning::pointers_directly_distinct_for_store`), and a miss forgets the
//! value. The implicit tail reads here which index disequalities would have
//! kept the forgotten cells, proves the ones it can before the statement, and
//! runs the statement again. A requested `--trace-proof` reads the same
//! inspection to show which cells a traced step dropped. Checking never calls
//! this.
use crate::kernel::primitives::SnapshotMapChange;
use crate::kernel::{CMemory, CompareRelation, Pointer, Proposition};

/// One cached cell a statement forgot beside a store into the same array.
pub(crate) struct ForgottenStoreCell {
    /// The cached cell the statement no longer holds.
    pub(crate) cell: Pointer,
    /// The cell the statement wrote beside it.
    pub(crate) store: Pointer,
    /// The fact the store-time check reads: the two element indices differ.
    pub(crate) indices_differ: Proposition,
}

/// How many (forgotten cell, written cell) pairs one inspection compares.
const MAX_COMPARED_PAIRS: usize = 64;

/// The cells `before` caches that `after` no longer holds, paired with each
/// cell `after` gained or changed in the same block at another element index
/// of a common base. Only the cells on which the two memories differ are
/// visited (the persistent concrete maps' diff skips shared subtrees; run
/// slots are not inspected), at most
/// [`MAX_COMPARED_PAIRS`] pairs are compared, and at most `limit` returned.
pub(crate) fn cells_forgotten_beside_stores(
    before: &CMemory,
    after: &CMemory,
    limit: usize,
) -> Vec<ForgottenStoreCell> {
    let mut forgotten = Vec::new();
    let mut written = Vec::new();
    // Only concrete cells: a seeded run's slots are never laid out here, so
    // a store into a long run costs its concrete changes alone.
    for change in before.cells.concrete().diff(after.cells.concrete()) {
        crate::instrumentation::record_deterministic_work(1);
        match change {
            SnapshotMapChange::Removed(pointer) => forgotten.push(pointer),
            SnapshotMapChange::Added(pointer) | SnapshotMapChange::Changed(pointer) => {
                written.push(pointer)
            }
        }
    }
    let mut pairs = Vec::new();
    let mut compared = 0usize;
    for cell in forgotten {
        for store in &written {
            if pairs.len() >= limit || compared >= MAX_COMPARED_PAIRS {
                return pairs;
            }
            compared += 1;
            crate::instrumentation::record_deterministic_work(1);
            let Some((cell_index, store_index, _)) =
                crate::kernel::reasoning::common_base_element_indices(cell, store)
            else {
                continue;
            };
            let equal = crate::kernel::assumptions::index_comparison(
                CompareRelation::Equal,
                store_index.operand_view(),
                cell_index.operand_view(),
            );
            pairs.push(ForgottenStoreCell {
                cell: cell.clone(),
                store: (*store).clone(),
                indices_differ: Proposition::ConditionIs(equal, false),
            });
        }
    }
    pairs
}
