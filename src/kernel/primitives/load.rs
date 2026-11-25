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

use super::{AddressBase, OldAddress, OldAddressOffset, ProgramPoint};

/// One load: a cell's bytes at a version point, interned by
/// `(point.read_key(), cell)`. The term carries its point and cell, so
/// decoding it needs no registry lookup.
#[derive(Clone)]
pub struct Load {
    node: Arc<LoadNode>,
}

struct LoadNode {
    id: u64,
    /// The hash of the point, as `ProgramPoint` hashes, and the cell, before
    /// probing: independent of what the session interned before, so it
    /// orders loads deterministically in one comparison.
    content: u64,
    /// The selection the load was first built from. Any other selection
    /// with the same read key names the same bytes (`design/loads.md`, open
    /// question 2): an `Exact` and an `IndexedCell` selection of one point
    /// are one load, as integer reads compare only `read_key()`.
    point: ProgramPoint,
    cell: OldAddress,
}

// A load's point holds memory whose cells hold addresses, which can hold
// loads: the auto-trait check of `Send` and `Sync` through that cycle
// overflows in downstream crates. Both parts are `Send` and `Sync` (asserted
// below without the cycle), so the node is.
//
// SAFETY: `LoadNode` owns an id, a `ProgramPoint` and an `OldAddress`, and has
// no interior mutability of its own; `assert_parts_thread_safe` checks that
// both parts are `Send + Sync`.
unsafe impl Send for LoadNode {}
// SAFETY: as above.
unsafe impl Sync for LoadNode {}

#[allow(dead_code, reason = "a compile-time check, never called")]
fn assert_parts_thread_safe() {
    fn thread_safe<T: Send + Sync>() {}
    thread_safe::<ProgramPoint>();
    thread_safe::<OldAddress>();
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
    pub(crate) fn at(point: ProgramPoint, cell: &OldAddress) -> Self {
        use std::hash::{Hash, Hasher};
        // Terms of two memory arenas never meet: an arena starts only with a
        // verification session, which also clears this interner, and a
        // `Load` keys a legacy point by arena id where `ProgramPoint`
        // compared memories by content.
        #[cfg(test)]
        if point.read_version_id().is_none() && !CROSS_ARENA_LOADS.with(std::cell::Cell::get) {
            assert_eq!(
                point.shared_memory().arena_id().0,
                super::memory_arena_token(),
                "a load of a memory from another arena"
            );
        }
        let key = point.read_key();
        // The slot hashes the point as `ProgramPoint` hashes, not its read
        // key: a legacy read key holds the arena token, which depends on how
        // many sessions started before, so hashing it would make ids, and
        // the hashes of every term holding a load, vary from run to run.
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        point.hash(&mut hasher);
        cell.hash(&mut hasher);
        let content = hasher.finish();
        let mut slot = content % LOAD_ID_RANGE;
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
                                content,
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
    pub(crate) fn address(&self) -> OldAddress {
        OldAddress {
            base: self.base(),
            offset: OldAddressOffset::Constant(0),
        }
    }

    /// The selection the load was first built from. Its read key is the
    /// load's; its kind (exact, indexed, entry) is whichever came first.
    pub(crate) fn point(&self) -> &ProgramPoint {
        &self.node.point
    }

    /// The cell whose bytes are loaded.
    pub(crate) fn cell(&self) -> &OldAddress {
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

/// Ordering is by content, never by id: proof search is sensitive to
/// iteration order, and an id is a probe slot that depends on what the
/// session interned before. Two loads compare by their content hash, and on
/// a tie by point (`ProgramPoint`'s order, by memory content for a legacy
/// point) and then cell. One id is one point key and cell, so this agrees
/// with equality; the id breaks only the tie of equal-content memories of two
/// arenas, which never meet in one proof.
impl Ord for Load {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.node.id == other.node.id {
            return std::cmp::Ordering::Equal;
        }
        self.node
            .content
            .cmp(&other.node.content)
            .then_with(|| self.node.point.cmp(&other.node.point))
            .then_with(|| self.node.cell.cmp(&other.node.cell))
            .then_with(|| self.node.id.cmp(&other.node.id))
    }
}

impl std::fmt::Debug for Load {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Load({})", self.node.id)
    }
}

/// The point the producer of an integer or float read selected
/// (`OldMachineTerm::MemoryLoad`'s first field). Consumers branch on its
/// selection kind (entry, exact, indexed write); it is no part of the term's
/// identity, which its [`LoadCell`] holds, so it compares equal to every
/// other read point, as [`super::AddressObjectClass`] does.
///
/// Built only beside its [`LoadCell`], by [`read_operands`].
#[derive(Clone)]
pub struct ReadPoint(ProgramPoint);

impl ReadPoint {
    /// The producer's point.
    pub(crate) fn point(&self) -> &ProgramPoint {
        &self.0
    }
}

impl std::ops::Deref for ReadPoint {
    type Target = ProgramPoint;
    fn deref(&self) -> &ProgramPoint {
        &self.0
    }
}

impl From<ReadPoint> for ProgramPoint {
    fn from(point: ReadPoint) -> Self {
        point.0
    }
}

impl From<&ReadPoint> for ProgramPoint {
    fn from(point: &ReadPoint) -> Self {
        point.0.clone()
    }
}

impl PartialEq for ReadPoint {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for ReadPoint {}

impl std::hash::Hash for ReadPoint {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for ReadPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ReadPoint {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl std::fmt::Debug for ReadPoint {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// The cell of an integer or float read (`OldMachineTerm::MemoryLoad`'s second
/// field): the address as the producer spelled it, and the interned [`Load`]
/// of that address at the producer's point. The load is the term's identity
/// (`design/loads.md`, step 3a): equality, hashing and ordering compare its
/// id, never the address, which the load's identity already holds.
///
/// Built only by [`read_operands`], so a rewritten address always comes with
/// the load of the rewritten cell.
#[derive(Clone)]
pub struct LoadCell {
    load: Load,
    address: Box<OldAddress>,
}

impl LoadCell {
    /// The read's interned load. Its [`Load::point`] is the first selection
    /// of its read key, not necessarily this read's: consumers read the
    /// selection from the term's own [`ReadPoint`].
    pub(crate) fn load(&self) -> &Load {
        &self.load
    }

    /// The address as the producer spelled it.
    pub(crate) fn address(&self) -> &OldAddress {
        &self.address
    }

    /// The address as the producer spelled it, boxed.
    pub(crate) fn boxed(&self) -> Box<OldAddress> {
        self.address.clone()
    }
}

impl std::ops::Deref for LoadCell {
    type Target = OldAddress;
    fn deref(&self) -> &OldAddress {
        &self.address
    }
}

impl AsRef<OldAddress> for LoadCell {
    fn as_ref(&self) -> &OldAddress {
        &self.address
    }
}

impl From<LoadCell> for Box<OldAddress> {
    fn from(cell: LoadCell) -> Self {
        cell.address
    }
}

impl From<&LoadCell> for Box<OldAddress> {
    fn from(cell: &LoadCell) -> Self {
        cell.address.clone()
    }
}

impl From<LoadCell> for OldAddress {
    fn from(cell: LoadCell) -> Self {
        *cell.address
    }
}

impl From<&LoadCell> for OldAddress {
    fn from(cell: &LoadCell) -> Self {
        (*cell.address).clone()
    }
}

impl PartialEq for LoadCell {
    fn eq(&self, other: &Self) -> bool {
        self.load == other.load
    }
}

impl Eq for LoadCell {}

impl std::hash::Hash for LoadCell {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.load.hash(state);
    }
}

impl PartialOrd for LoadCell {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LoadCell {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.load.cmp(&other.load)
    }
}

impl std::fmt::Debug for LoadCell {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.address.fmt(formatter)
    }
}

/// The operands of the integer or float read of `address` at `point`: the
/// producer's point, and the address with its interned load. The one builder
/// of [`ReadPoint`] and [`LoadCell`], called by `OldMachineTerm::read_named`;
/// `build_support/read_construction.rs` keeps it so.
pub(crate) fn read_operands(
    point: ProgramPoint,
    address: Box<OldAddress>,
) -> (ReadPoint, LoadCell) {
    let load = Load::at(point.clone(), &address);
    (ReadPoint(point), LoadCell { load, address })
}

/// The eight-byte integer read the legacy scalar machinery takes in place of
/// a pointer cell: the memory-named read of `cell` in `memory` at
/// `LoadKind::Bits64` (`design/loads.md`, step 3b, PR 1).
///
/// A pointer load is named, compared and keyed as a [`Load`]. Two consumers
/// still ask the integer read machinery about a pointer cell, because that
/// machinery has no form keyed by a load:
///
/// - `OldAddress::canonical_read` and `OldAddress::canonical_loaded_value` select
///   the cell's version through `canonical_scalar_read`, whose identity
///   cache, read observations and access widths are keyed by
///   `(memory, address, kind)` and shared with 64-bit integer reads of the
///   cell;
/// - `pointers_equal_with_load_atoms` compares two load bases through the
///   caller's load-atom rule, whose fact-dependent forms
///   (`memory_loads_proven_equal`, the quantified frame's unchanged-load
///   rule) decide frame equality of integer reads.
///
/// Both go through this one bridge, so that splitting `Bits64` into signed
/// and unsigned formats has one place to replace.
/// `build_support/read_construction.rs` counts its callers.
///
/// A caller that knows where the read was made passes that point as `site`;
/// the read records it (`ProgramPoint::at_read_site`) and is the same term.
pub(crate) fn legacy_pointer_word_read(
    memory: &crate::kernel::SharedMemory,
    site: Option<&ProgramPoint>,
    cell: &OldAddress,
) -> crate::kernel::OldMachineTerm {
    crate::kernel::OldMachineTerm::read_named(
        ProgramPoint::read_at_optional(memory, site),
        cell.clone(),
        crate::kernel::LoadKind::Bits64,
    )
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

#[cfg(test)]
thread_local! {
    static CROSS_ARENA_LOADS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Lets a test that probes the arena boundary build loads of an earlier
/// arena's memory until the guard drops; elsewhere `Load::at` asserts that
/// a legacy point's memory is the current arena's.
#[cfg(test)]
pub(crate) fn allow_cross_arena_loads() -> impl Drop {
    struct Allow(bool);
    impl Drop for Allow {
        fn drop(&mut self) {
            CROSS_ARENA_LOADS.with(|allowed| allowed.set(self.0));
        }
    }
    Allow(CROSS_ARENA_LOADS.with(|allowed| allowed.replace(true)))
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
