//! The identity of a load (`design/loads.md`, "Terms").
//!
//! A load is the bytes of a cell at a version point. Its identity is the
//! point's read key (`Memory`, `Point` or `View`) and the cell, and nothing
//! else: not the type it is decoded at, not whether its point was selected
//! exactly or as an indexed version, and never the whole `ProgramPoint`,
//! whose `IndexedWrite` selection holds a derivation. Interning gives one
//! [`Load`] per identity, so equality, hashing and ordering compare one
//! number.
//!
//! [`Load::at`] is the only constructor, and [`Load::base`] the only builder
//! of [`AddressBase::Load`]; `build_support/read_construction.rs` keeps it so.

use std::sync::Arc;

use super::{Address, AddressBase, AddressOffset, ProgramPoint};

/// One load: a cell's bytes at a version point, interned by
/// `(point.read_key(), cell)`. The term carries its point and cell, so
/// decoding it needs no registry lookup.
#[derive(Clone)]
pub struct Load {
    node: Arc<LoadNode>,
}

struct LoadNode {
    id: u64,
    /// The selection the load was first built from. Any other selection
    /// with the same read key names the same bytes (`design/loads.md`, open
    /// question 2): an `Exact` and an `IndexedCell` selection of one point
    /// are one load, as integer reads compare only `read_key()`.
    point: ProgramPoint,
    cell: Address,
}

// A load's point holds memory whose cells hold addresses, which can hold
// loads: the auto-trait check of `Send` and `Sync` through that cycle
// overflows in downstream crates. Both parts are `Send` and `Sync` (asserted
// below without the cycle), so the node is.
//
// SAFETY: `LoadNode` owns an id, a `ProgramPoint` and an `Address`, and has
// no interior mutability of its own; `assert_parts_thread_safe` checks that
// both parts are `Send + Sync`.
unsafe impl Send for LoadNode {}
// SAFETY: as above.
unsafe impl Sync for LoadNode {}

#[allow(dead_code, reason = "a compile-time check, never called")]
fn assert_parts_thread_safe() {
    fn thread_safe<T: Send + Sync>() {}
    thread_safe::<ProgramPoint>();
    thread_safe::<Address>();
}

/// How many slots load identities are hashed into. The capacity below
/// dwarfs no real session; a collision only probes to the next slot.
const LOAD_ID_RANGE: u64 = 1 << 40;

/// The most loads one verification session may intern. Exhausting it is a
/// loud verifier failure, never a silent clear: two live loads must never
/// share an id.
const LOAD_INTERNER_CAPACITY: usize = 1_000_000;

thread_local! {
    /// Interned loads by id. The id is the first free slot at or after the
    /// hash of the identity, so it is deterministic for a session's
    /// sequence of loads and independent of the selection that names them.
    static LOAD_INTERNER: std::cell::RefCell<std::collections::HashMap<u64, Load>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

impl Load {
    /// The load of `cell` at `point`. The one constructor: the identity is
    /// the point's read key and the cell; a later selection with the same
    /// key returns the load already interned, keeping its first point.
    pub(crate) fn at(point: ProgramPoint, cell: &Address) -> Self {
        use std::hash::{Hash, Hasher};
        let key = point.read_key();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        cell.hash(&mut hasher);
        let mut slot = hasher.finish() % LOAD_ID_RANGE;
        LOAD_INTERNER.with(|interner| {
            let mut interner = interner.borrow_mut();
            loop {
                match interner.get(&slot) {
                    Some(known)
                        if known.node.point.read_key() == key && known.node.cell == *cell =>
                    {
                        return known.clone();
                    }
                    Some(_) => {
                        crate::instrumentation::record_deterministic_work(1);
                        slot = (slot + 1) % LOAD_ID_RANGE;
                    }
                    None => {
                        assert!(
                            interner.len() < LOAD_INTERNER_CAPACITY,
                            "load interner capacity exhausted"
                        );
                        let load = Load {
                            node: Arc::new(LoadNode {
                                id: slot,
                                point,
                                cell: cell.clone(),
                            }),
                        };
                        interner.insert(slot, load.clone());
                        return load;
                    }
                }
            }
        })
    }

    /// This load as a pointer's address base: the opaque pointer whose
    /// address and provenance the load names (`design/loads.md`, "Pointers").
    /// The one builder of [`AddressBase::Load`].
    pub(crate) fn base(&self) -> AddressBase {
        AddressBase::Load(self.clone())
    }

    /// The pointer address this load holds, undisplaced.
    pub(crate) fn address(&self) -> Address {
        Address {
            base: self.base(),
            offset: AddressOffset::Constant(0),
        }
    }

    /// The selection the load was first built from. Its read key is the
    /// load's; its kind (exact, indexed, entry) is whichever came first.
    pub(crate) fn point(&self) -> &ProgramPoint {
        &self.node.point
    }

    /// The cell whose bytes are loaded.
    pub(crate) fn cell(&self) -> &Address {
        &self.node.cell
    }

    /// The interned identity, for keys and printing.
    pub(crate) fn id(&self) -> u64 {
        self.node.id
    }

    /// Whether a version point names the load, rather than a memory state's
    /// unchanged-bytes source (`ReadKey::Memory`, the legacy form).
    pub(crate) fn is_point_named(&self) -> bool {
        self.node.point.read_version_id().is_some()
    }
}

impl PartialEq for Load {
    fn eq(&self, other: &Self) -> bool {
        self.node.id == other.node.id
    }
}

impl Eq for Load {}

impl std::hash::Hash for Load {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.node.id.hash(state);
    }
}

impl PartialOrd for Load {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Load {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.node.id.cmp(&other.node.id)
    }
}

impl std::fmt::Debug for Load {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Load({})", self.node.id)
    }
}

/// The interned loads, as one value a reusable session captures and
/// restores with the rest of the load registry state.
#[derive(Clone, Default)]
pub(crate) struct LoadInternerState(std::collections::HashMap<u64, Load>);

pub(crate) fn capture_load_interner() -> LoadInternerState {
    LOAD_INTERNER.with(|interner| LoadInternerState(interner.borrow().clone()))
}

pub(crate) fn restore_load_interner(state: &LoadInternerState) {
    LOAD_INTERNER.with(|interner| *interner.borrow_mut() = state.0.clone());
}

pub(crate) fn clear_load_interner() {
    LOAD_INTERNER.with(|interner| interner.borrow_mut().clear());
}

/// How many loads are interned.
#[cfg(test)]
pub(crate) fn interned_load_count() -> usize {
    LOAD_INTERNER.with(|interner| interner.borrow().len())
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/load.rs");
}
