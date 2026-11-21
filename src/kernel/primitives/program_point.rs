//! The program point: a node a proof path reached.
//!
//! A [`ProgramPoint`] carries the memory state there and its place on the
//! path: an identity minted at each memory transition, linked to the point or
//! points it was reached from. SymbolicMemory states are interned by content, so two
//! paths that reach equal memory share one state; their points are still two.
//!
//! Surface records the name of each point it records a state at
//! (`RecordedStates::point_name`).

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Weak};

use crate::persistent::PersistentMap;

use super::{
    Address, AddressBase, AddressOffset, LoadKind, MachineTerm, MemoryDerivation, MemoryRange,
    ProgramType, ProgramValue, SharedMemory, StoredMemoryValue, SymbolicMemory, intern_memory,
    intern_memory_ref,
};

/// The identity of one point an execution path reached.
///
/// Identities are unique within a process and carry no order: no decision
/// may depend on comparing two of them other than for equality. Ordering is
/// provided solely for exact fact keys.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ProgramPointId(u64);

static NEXT_PROGRAM_POINT_ID: AtomicU64 = AtomicU64::new(1);

impl ProgramPointId {
    fn fresh() -> Self {
        Self(NEXT_PROGRAM_POINT_ID.fetch_add(1, Ordering::Relaxed))
    }
}

/// The steps a path took between two points, newest first: each recorded
/// memory step and the memory it produced.
///
/// A step is added where it is recorded ([`super::record_memory_derivation`])
/// to the log of the memory value the path is executing, so the log follows
/// the path that ran even when the arena shares the resulting content with
/// another path. The point a state reaches next takes the log.
pub(crate) struct StepLog {
    step: Arc<MemoryDerivation>,
    produced: SharedMemory,
    previous: Option<Arc<StepLog>>,
    named_cells_origin: Option<NamedCellsOrigin>,
    first_base: SharedMemory,
    contiguous: bool,
    preserves_external_storage: bool,
}

/// The exact source of a suffix that only names existing cells. The log
/// retains the earlier steps, so their identity is available without walking.
#[derive(Clone)]
struct NamedCellsOrigin {
    memory: (u32, u32),
    previous: Option<Weak<StepLog>>,
}

impl NamedCellsOrigin {
    fn of(memory: &SharedMemory, steps: Option<&Arc<StepLog>>) -> Self {
        if let Some(steps) = steps
            && steps.produced.arena_id() == memory.arena_id()
            && let Some(origin) = &steps.named_cells_origin
        {
            return origin.clone();
        }
        Self {
            memory: memory.arena_id(),
            previous: steps.map(Arc::downgrade),
        }
    }
}

impl StepLog {
    /// `previous` with `step`, which produced `produced`, added as newest.
    pub(crate) fn push(
        previous: Option<Arc<Self>>,
        step: Arc<MemoryDerivation>,
        produced: SharedMemory,
        names_existing_cells: bool,
    ) -> Arc<Self> {
        let named_cells_origin =
            names_existing_cells.then(|| NamedCellsOrigin::of(step.base(), previous.as_ref()));
        let (first_base, contiguous) = previous.as_ref().map_or_else(
            || (step.base().clone(), true),
            |prefix| {
                (
                    prefix.first_base.clone(),
                    prefix.contiguous && prefix.produced.arena_id() == step.base().arena_id(),
                )
            },
        );
        let preserves_external_storage = previous
            .as_ref()
            .is_none_or(|old| old.preserves_external_storage)
            && match step.as_ref() {
                MemoryDerivation::Store { pointer, .. }
                | MemoryDerivation::RepresentationWrite { pointer, .. } => {
                    indexed_local(&pointer.base)
                }
                // A declaration makes fresh storage: a local, or the
                // temporary a call result is built in.
                MemoryDerivation::BlockDeclared { block, .. } => {
                    indexed_local(block) || matches!(block, AddressBase::Temporary(_))
                }
                MemoryDerivation::LocalLifetimeEnded { block, .. } => indexed_local(block),
                MemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(ranges),
                    ..
                } => ranges.iter().all(|range| {
                    crate::instrumentation::record_deterministic_work(1);
                    indexed_local(&range.base().base)
                }),
                _ => names_existing_cells,
            };
        Arc::new(Self {
            step,
            produced,
            previous,
            named_cells_origin,
            first_base,
            contiguous,
            preserves_external_storage,
        })
    }

    /// Whether the replacement extends this view with naming alone. Even a
    /// real store that restores the same contents has a different log prefix.
    pub(super) fn materializes_from(
        source: &SharedMemory,
        source_steps: Option<&Arc<Self>>,
        replacement: &SharedMemory,
        replacement_steps: Option<&Arc<Self>>,
    ) -> bool {
        if source.arena_id() == replacement.arena_id()
            && source_steps.map(Arc::as_ptr) == replacement_steps.map(Arc::as_ptr)
        {
            return true;
        }
        let Some(steps) = replacement_steps else {
            return false;
        };
        let Some(origin) = &steps.named_cells_origin else {
            return false;
        };
        let before = NamedCellsOrigin::of(source, source_steps);
        steps.produced.arena_id() == replacement.arena_id()
            && origin.memory == before.memory
            && origin.previous.as_ref().map(Weak::as_ptr)
                == before.previous.as_ref().map(Weak::as_ptr)
    }

    /// The steps, newest first, each with the memory it produced.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn newest_first(&self) -> impl Iterator<Item = (&MemoryDerivation, &SharedMemory)> {
        std::iter::successors(Some(self), |log| log.previous.as_deref())
            .map(|log| (log.step.as_ref(), &log.produced))
    }
}

impl std::fmt::Debug for StepLog {
    /// A count, not the steps: a log can be long and its memories large.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let count = std::iter::successors(Some(self), |log| log.previous.as_deref()).count();
        write!(f, "StepLog({count} steps)")
    }
}

impl Drop for StepLog {
    /// Drop a long log one step at a time.
    fn drop(&mut self) {
        let mut previous = self.previous.take();
        while let Some(log) = previous {
            previous = match Arc::try_unwrap(log) {
                Ok(mut log) => log.previous.take(),
                Err(_) => None,
            };
        }
    }
}

type PointReadObjects = PersistentMap<AddressBase, PointReadObject>;
type PointReadCells = PersistentMap<i64, PointReadWrite>;

#[derive(Clone, Debug)]
struct PointReadIndex {
    /// A wholesale barrier ends the shared index lineage.
    generation: ProgramPointId,
    blocks: PointReadObjects,
}

impl PointReadIndex {
    fn empty(generation: ProgramPointId) -> Self {
        Self {
            generation,
            blocks: PointReadObjects::default(),
        }
    }
}

#[derive(Clone, Debug)]
struct PointReadObject {
    /// A whole-object removal can discard an arbitrarily large map. A later
    /// write creates a new lineage so the join need not diff those maps.
    generation: ProgramPointId,
    origin: Option<(AddressBase, AddressOffset)>,
    cells: PointReadCells,
}

impl PartialEq for PointReadObject {
    fn eq(&self, other: &Self) -> bool {
        self.generation == other.generation
            && self.origin == other.origin
            && self.cells.shares_root_with(&other.cells)
    }
}

#[derive(Clone, Debug)]
struct PointReadWrite {
    end: i64,
    version: Weak<PointNode>,
    source: Arc<MemoryDerivation>,
}

impl PartialEq for PointReadWrite {
    fn eq(&self, other: &Self) -> bool {
        self.end == other.end
            && Weak::ptr_eq(&self.version, &other.version)
            && Arc::ptr_eq(&self.source, &other.source)
    }
}

#[derive(Debug)]
struct PointNode {
    id: ProgramPointId,
    function_entry: bool,
    /// The memory state the path had here.
    memory: SharedMemory,
    /// The steps the path took from its predecessor to here, newest first;
    /// none when it reached here without a recorded step.
    steps: Option<Arc<StepLog>>,
    /// The points this one was reached from on its path: one after an
    /// ordinary transition, two after a branch join, none at the start.
    predecessors: Box<[PathLink]>,
    /// For a branch join, the point where its arms split.
    split: Option<PathLink>,
    /// Disjoint typed cells, keyed by storage and byte start. The
    /// predecessor chain owns the version points.
    point_read_index: PointReadIndex,
    /// Earliest recorded view in a suffix of effects disjoint from parameter
    /// storage. Read selection can start here.
    external_read_start: Option<ExternalReadStart>,
    /// Entry carried across this point's checked call. The ordinary local
    /// suffix can reach this point without admitting the call for scalar reads.
    array_entry_after_call: Option<ExternalReadStart>,
}

#[derive(Clone, Debug)]
struct ExternalReadStart {
    point: Weak<PointNode>,
    view: IndexedView,
    memory: SharedMemory,
}

impl Drop for PointNode {
    /// A long path is a long chain; dropping it one link at a time keeps the
    /// stack flat however many transitions the path made.
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.predecessors).into_vec();
        pending.extend(self.split.take());
        while let Some(PathLink(node, _)) = pending.pop() {
            if let Some(node) = node
                && let Ok(mut node) = Arc::try_unwrap(node)
            {
                pending.extend(std::mem::take(&mut node.predecessors).into_vec());
                pending.extend(node.split.take());
            }
        }
    }
}

/// Where on its path a point is: its identity and the points it was reached
/// from, or none for a point built from a bare memory or a state before its
/// first memory transition. An [`super::ExecutionState`] carries the one for
/// the point it stands at.
///
/// It is not part of a state's equality, hashing or order: two states are
/// equal when they hold the same things, wherever each was reached.
#[derive(Clone, Debug, Default)]
pub(crate) struct PathLink(Option<Arc<PointNode>>, IndexedView);

#[derive(Clone, Copy, PartialEq, Eq)]
enum PointTransition {
    FunctionEntry,
    Execution,
    Provisional,
    LoopHead,
}

/// Which view may use the execution point's versions. Proof-local views may
/// differ between copies of a path, so this is held on the link, not the node.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum IndexedView {
    #[default]
    Recorded,
    Materialized((u32, u32)),
    Unverified,
}

impl PathLink {
    pub(in crate::kernel) fn shares_point_and_view(&self, other: &Self) -> bool {
        self.id() == other.id() && self.1 == other.1
    }

    pub(in crate::kernel) fn matches_indexed_view(&self, memory: &SharedMemory) -> bool {
        match self.1 {
            IndexedView::Recorded => self
                .0
                .as_ref()
                .is_some_and(|node| node.memory.arena_id() == memory.arena_id()),
            IndexedView::Materialized(view) => view == memory.arena_id(),
            IndexedView::Unverified => false,
        }
    }

    /// Bind the memory view being constructed for an entry root. There are
    /// no preceding execution versions to carry into this view.
    pub(super) fn with_entry_view(mut self, view: &SharedMemory) -> Self {
        assert!(
            self.0
                .as_ref()
                .is_some_and(|point| { point.predecessors.is_empty() && point.steps.is_none() })
        );
        self.1 = IndexedView::Materialized(view.arena_id());
        self
    }

    pub(super) fn with_materialized_view(
        mut self,
        source: &SharedMemory,
        view: &SharedMemory,
        verified: bool,
    ) -> Self {
        if !verified || !self.matches_indexed_view(source) {
            self.1 = IndexedView::Unverified;
        } else if source.arena_id() != view.arena_id() {
            self.1 = IndexedView::Materialized(view.arena_id());
        }
        self
    }

    pub(super) fn function_entry(memory: SharedMemory) -> Self {
        Self::reached_from(
            memory,
            None,
            Box::new([]),
            None,
            PointTransition::FunctionEntry,
        )
    }

    /// A new point reached from this one by `steps`, where the path has
    /// `memory`.
    ///
    /// A path that has no point yet begins where its first step began: a
    /// state set up by steps before it first stands at a point (an entry
    /// state whose precondition observed cells) gets a point at the memory
    /// before them, so a walk back can cross them as it crosses any step.
    pub(crate) fn after(&self, memory: SharedMemory, steps: Option<Arc<StepLog>>) -> Self {
        self.after_with_index(memory, steps, PointTransition::Execution)
    }

    pub(super) fn after_loop_head(
        &self,
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
    ) -> Self {
        self.after_with_index(memory, steps, PointTransition::LoopHead)
    }

    fn after_with_index(
        &self,
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
        transition: PointTransition,
    ) -> Self {
        let from = match (&self.0, &steps) {
            (None, Some(log)) => Self::reached_from(
                log.first_base.clone(),
                None,
                Box::new([]),
                None,
                PointTransition::Provisional,
            ),
            _ => self.clone(),
        };
        Self::reached_from(memory, steps, Box::new([from]), None, transition)
    }

    /// A new point where two arms that split at `split` rejoin with
    /// `memory`.
    pub(crate) fn joining(
        left: ProgramPoint,
        right: ProgramPoint,
        split: &Self,
        memory: SharedMemory,
    ) -> Self {
        Self::joining_points(&[left, right], Some(split), memory)
    }

    pub(super) fn joining_points(
        points: &[ProgramPoint],
        split: Option<&Self>,
        memory: SharedMemory,
    ) -> Self {
        let predecessors = points
            .iter()
            .map(|point| point.path.clone())
            .collect::<Box<[_]>>();
        let id = ProgramPointId::fresh();
        let point_read_index =
            join_point_read_indexes(points).unwrap_or_else(|| PointReadIndex::empty(id));
        let external_read_start = joined_external_entry(points);
        Self(
            Some(Arc::new(PointNode {
                id,
                function_entry: false,
                memory,
                steps: None,
                predecessors,
                split: split.filter(|point| point.0.is_some()).cloned(),
                point_read_index,
                external_read_start,
                array_entry_after_call: None,
            })),
            IndexedView::Recorded,
        )
    }

    fn reached_from(
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
        predecessors: Box<[PathLink]>,
        split: Option<PathLink>,
        transition: PointTransition,
    ) -> Self {
        let predecessors = predecessors
            .into_vec()
            .into_iter()
            .filter(|point| point.0.is_some())
            .collect::<Box<[_]>>();
        let external_read_start = external_read_start(&predecessors, steps.as_deref(), &memory);
        let array_entry_after_call =
            array_entry_across_call(&predecessors, steps.as_deref(), &memory);
        Self(
            Some(Arc::new_cyclic(|version| {
                let id = ProgramPointId::fresh();
                let point_read_index = point_read_index(
                    &predecessors,
                    steps.as_deref(),
                    &memory,
                    version,
                    id,
                    transition,
                );
                PointNode {
                    id,
                    function_entry: transition == PointTransition::FunctionEntry,
                    memory,
                    steps,
                    predecessors,
                    split: split.filter(|point| point.0.is_some()),
                    point_read_index,
                    external_read_start,
                    array_entry_after_call,
                }
            })),
            IndexedView::Recorded,
        )
    }

    /// The steps the path took from its predecessor to this point.
    pub(crate) fn steps(&self) -> Option<&StepLog> {
        self.0.as_ref().and_then(|node| node.steps.as_deref())
    }

    /// For a branch join, the point where its arms split.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn split(&self) -> Option<&Self> {
        self.0.as_ref().and_then(|node| node.split.as_ref())
    }

    /// The memory state the path had at this point.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn memory(&self) -> Option<&SharedMemory> {
        self.0.as_ref().map(|node| &node.memory)
    }

    /// The points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessors(&self) -> &[Self] {
        self.0
            .as_ref()
            .map(|node| node.predecessors.as_ref())
            .unwrap_or(&[])
    }

    pub(crate) fn id(&self) -> Option<ProgramPointId> {
        self.0.as_ref().map(|node| node.id)
    }

    /// The identities of the points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessor_ids(&self) -> Vec<ProgramPointId> {
        self.0
            .as_ref()
            .map(|node| node.predecessors.iter().filter_map(Self::id).collect())
            .unwrap_or_default()
    }
}

// Two automatic blocks with different identities are structurally disjoint.
fn indexed_local(block: &AddressBase) -> bool {
    matches!(block, AddressBase::AutomaticLocal { .. })
        || matches!(block, AddressBase::Concrete(_) if block.is_local_block())
}

/// Parameter addresses can alias across differently written bases. Keep one
/// parameter base and one symbolic offset origin in the shared parameter bucket.
fn external_storage(block: &AddressBase) -> bool {
    matches!(
        block,
        AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
    )
}

fn read_bucket(block: &AddressBase) -> Option<&AddressBase> {
    if external_storage(block) {
        Some(&AddressBase::ExternalArgument)
    } else if indexed_local(block) || matches!(block, AddressBase::Heap(_)) {
        Some(block)
    } else {
        None
    }
}

/// The bounded address shape only. No arithmetic or alias fact is consulted.
/// Symbolic offsets share a bucket only while they use the same origin.
fn read_displacement(offset: &AddressOffset) -> Option<(Option<&AddressOffset>, i64)> {
    match offset {
        AddressOffset::Constant(start) => Some((None, *start)),
        AddressOffset::Add(origin, delta)
            if origin.is_shallow()
                && let AddressOffset::Constant(delta) = delta.as_ref() =>
        {
            Some((Some(origin), *delta))
        }
        AddressOffset::Add(delta, origin)
            if origin.is_shallow()
                && let AddressOffset::Constant(delta) = delta.as_ref() =>
        {
            Some((Some(origin), *delta))
        }
        _ if offset.is_shallow() => Some((Some(offset), 0)),
        _ => None,
    }
}

fn read_origin(
    pointer: &Address,
    anchor: Option<&AddressOffset>,
) -> Option<(AddressBase, AddressOffset)> {
    if anchor.is_some() || external_storage(&pointer.base) {
        Some((
            pointer.base.clone(),
            anchor.cloned().unwrap_or(AddressOffset::Constant(0)),
        ))
    } else {
        None
    }
}

/// Intersect the versions carried by each checked incoming point. Diff each
/// arm against the first arm, so an earlier removal is not revisited for
/// every later arm.
fn join_point_read_indexes(points: &[ProgramPoint]) -> Option<PointReadIndex> {
    fn index(point: &ProgramPoint) -> Option<&PointReadIndex> {
        let node = point.path.0.as_ref()?;
        point
            .path
            .matches_indexed_view(&point.memory)
            .then_some(&node.point_read_index)
    }

    let (first, rest) = points.split_first()?;
    let base = index(first)?;
    let mut result = base.clone();
    for point in rest {
        let other = index(point)?;
        if other.generation != base.generation {
            return None;
        }
        for (key, left, right) in base.blocks.diff(&other.blocks) {
            let (Some(left), Some(right), Some(mut kept)) =
                (left, right, result.blocks.get(key).cloned())
            else {
                result.blocks.remove(key);
                continue;
            };
            if left.generation != right.generation || left.origin != right.origin {
                result.blocks.remove(key);
                continue;
            }
            for (start, _, _) in left.cells.diff(&right.cells) {
                kept.cells.remove(start);
            }
            if kept.cells.is_empty() {
                result.blocks.remove(key);
            } else {
                result.blocks.insert(key.clone(), kept);
            }
        }
    }
    Some(result)
}

fn external_read_start(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
) -> Option<ExternalReadStart> {
    let [from @ PathLink(Some(point), view)] = predecessors else {
        return None;
    };
    let source = match steps {
        Some(log)
            if log.contiguous
                && log.preserves_external_storage
                && log.produced.arena_id() == memory.arena_id() =>
        {
            &log.first_base
        }
        Some(_) => return None,
        None => memory,
    };
    if !from.matches_indexed_view(source) {
        return None;
    }
    point.external_read_start.clone().or_else(|| {
        Some(ExternalReadStart {
            point: Arc::downgrade(point),
            view: view.clone(),
            memory: source.clone(),
        })
    })
}

/// A checked call with one write range in a fresh automatic object cannot
/// write any array supplied by a parameter. Use exactly that recorded edge.
fn array_entry_across_call(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
) -> Option<ExternalReadStart> {
    let [from] = predecessors else { return None };
    let log = steps?;
    if log.previous.is_some() || log.produced.arena_id() != memory.arena_id() {
        return None;
    }
    let MemoryDerivation::CallHavoc {
        mutable_ranges,
        base,
        ..
    } = log.step.as_ref()
    else {
        return None;
    };
    let [written] = mutable_ranges.as_slice() else {
        return None;
    };
    if !indexed_local(&written.base().base) {
        return None;
    }
    external_array_entry(from, base)
}

/// The ordinary local suffix may end at entry or at a call with a certified
/// entry. Either case is one suffix lookup and at most one further lookup.
fn external_array_entry(path: &PathLink, memory: &SharedMemory) -> Option<ExternalReadStart> {
    if !path.matches_indexed_view(memory) {
        return None;
    }
    let node = path.0.as_ref()?;
    if node.function_entry {
        return Some(ExternalReadStart {
            point: Arc::downgrade(node),
            view: path.1.clone(),
            memory: memory.clone(),
        });
    }
    if let Some(anchor) = &node.external_read_start {
        let origin = anchor.point.upgrade()?;
        return if origin.function_entry {
            Some(anchor.clone())
        } else {
            origin.array_entry_after_call.clone()
        };
    }
    node.array_entry_after_call.clone()
}

/// Retain the common entry only when every incoming path proves that it
/// preserved external storage. The incoming points already own the anchors.
fn joined_external_entry(points: &[ProgramPoint]) -> Option<ExternalReadStart> {
    let (first, rest) = points.split_first()?;
    let entry = external_array_entry(&first.path, &first.memory)?;
    for point in rest {
        crate::instrumentation::record_deterministic_work(1);
        let other = external_array_entry(&point.path, &point.memory)?;
        if !Weak::ptr_eq(&entry.point, &other.point)
            || entry.memory.arena_id() != other.memory.arena_id()
        {
            return None;
        }
    }
    Some(entry)
}

/// Apply the explicit effects once, when execution seals the point. A read
/// of a provisional point may index a single effect but never replays a batch.
fn point_read_index(
    predecessors: &[PathLink],
    steps: Option<&StepLog>,
    memory: &SharedMemory,
    version: &Weak<PointNode>,
    id: ProgramPointId,
    transition: PointTransition,
) -> PointReadIndex {
    let [from @ PathLink(Some(before), _)] = predecessors else {
        return PointReadIndex::empty(id);
    };
    let Some(step) = steps else {
        return if from.matches_indexed_view(memory) {
            before.point_read_index.clone()
        } else {
            PointReadIndex::empty(id)
        };
    };
    if (transition == PointTransition::Provisional && step.previous.is_some())
        || !step.contiguous
        || !from.matches_indexed_view(&step.first_base)
        || step.produced.arena_id() != memory.arena_id()
    {
        return PointReadIndex::empty(id);
    }
    let mut index = before.point_read_index.clone();
    let record_writes = transition != PointTransition::LoopHead;
    if step.previous.is_none() {
        record_point_read_effect(&mut index, &step.step, version, id, record_writes);
    } else {
        let effects =
            std::iter::successors(Some(step), |step| step.previous.as_deref()).collect::<Vec<_>>();
        for effect in effects.into_iter().rev() {
            record_point_read_effect(&mut index, &effect.step, version, id, record_writes);
        }
    }
    index
}

fn record_point_read_effect(
    index: &mut PointReadIndex,
    step: &Arc<MemoryDerivation>,
    version: &Weak<PointNode>,
    id: ProgramPointId,
    record_writes: bool,
) {
    crate::instrumentation::record_deterministic_work(1);
    match step.as_ref() {
        MemoryDerivation::Store { pointer, .. }
        | MemoryDerivation::RepresentationWrite { pointer, .. }
        | MemoryDerivation::ObjectInitializationRecorded {
            pointer,
            call_word: true,
            ..
        } if read_bucket(&pointer.base).is_some() => {
            let bucket = read_bucket(&pointer.base).expect("indexed write bucket");
            let call_word = matches!(
                step.as_ref(),
                MemoryDerivation::ObjectInitializationRecorded {
                    call_word: true,
                    ..
                }
            );
            let width = if call_word {
                i64::from(ProgramType::Int32.byte_width())
            } else {
                i64::from(step.single_write().expect("single checked write").1)
            };
            let Some((anchor, start)) = read_displacement(&pointer.offset) else {
                index.blocks.remove(bucket);
                return;
            };
            let Some(end) = start
                .checked_add(width)
                .filter(|_| (1..=super::MAX_SCALAR_ACCESS_BYTES).contains(&width))
            else {
                index.blocks.remove(bucket);
                return;
            };
            let origin = read_origin(pointer, anchor);
            let mut block = index
                .blocks
                .get(bucket)
                .filter(|block| block.origin == origin)
                .cloned()
                .unwrap_or_else(|| PointReadObject {
                    generation: id,
                    origin,
                    cells: PointReadCells::default(),
                });
            clear_overlapping_cells(&mut block.cells, start, end);
            if record_writes
                && (call_word
                    || integer_store_bits(step).is_some()
                    || matches!(step.as_ref(), MemoryDerivation::Store { value, .. }
                        if matches!(value.native(), ProgramValue::Bool(_) | ProgramValue::Pointer(_))
                            || (indexed_local(&pointer.base) && matches!(value.native(), ProgramValue::Parameter(_)))))
            {
                block.cells.insert(
                    start,
                    PointReadWrite {
                        end,
                        version: version.clone(),
                        source: step.clone(),
                    },
                );
            }
            if block.cells.is_empty() {
                index.blocks.remove(bucket);
            } else {
                index.blocks.insert(bucket.clone(), block);
            }
        }
        MemoryDerivation::CellsForgotten { .. }
        | MemoryDerivation::CellObserved { .. }
        | MemoryDerivation::BlockDeclared { .. }
        | MemoryDerivation::HeapAllocated { .. }
        | MemoryDerivation::HeapAllocationPending { .. }
        | MemoryDerivation::HeapAllocationFailed { .. }
        | MemoryDerivation::ContractAllocationClaimsChanged { .. }
        | MemoryDerivation::ObjectInitializationRecorded { .. } => {}
        MemoryDerivation::CallHavoc { mutable_ranges, .. }
        | MemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => {
            retain_outside_named_write_objects(index, mutable_ranges, id);
        }
        MemoryDerivation::LocalLifetimeEnded { block, .. } if indexed_local(block) => {
            index.blocks.remove(block);
        }
        MemoryDerivation::HeapFreed {
            allocation_base, ..
        }
        | MemoryDerivation::ContractAllocationRetired {
            allocation_base, ..
        } if read_bucket(&allocation_base.base).is_some() => {
            index
                .blocks
                .remove(read_bucket(&allocation_base.base).expect("indexed lifetime bucket"));
        }
        _ => *index = PointReadIndex::empty(id),
    }
}

/// These object identities are structurally distinct from every indexed
/// automatic object except that exact object. A checked range in such an
/// object can conservatively retire its whole bucket without visiting cells.
fn retain_outside_named_write_objects(
    index: &mut PointReadIndex,
    ranges: &[MemoryRange],
    id: ProgramPointId,
) {
    for range in ranges {
        crate::instrumentation::record_deterministic_work(1);
        let block = &range.base().base;
        if let Some(bucket) = read_bucket(block) {
            index.blocks.remove(bucket);
            continue;
        }
        match block {
            AddressBase::Temporary(_) => {}
            AddressBase::Concrete(_) | AddressBase::StaticObject { .. } => {
                index.blocks.remove(&AddressBase::ExternalArgument);
            }
            _ => {
                *index = PointReadIndex::empty(id);
                return;
            }
        }
    }
}

/// Disjoint intervals have at most one earlier start overlapping the write.
/// Every other hit starts inside the write, so a scalar write removes at most
/// its byte width plus one entry, regardless of the object's size.
fn clear_overlapping_cells(cells: &mut PointReadCells, start: i64, end: i64) {
    if let Some((&earlier, write)) = cells.get_less_than(&start)
        && write.end > start
    {
        cells.remove(&earlier);
    }
    if cells.contains_key(&start) {
        cells.remove(&start);
    }
    while let Some((&later, _)) = cells.get_greater_than(&start)
        && later < end
    {
        cells.remove(&later);
    }
}

fn integer_store_bits(step: &MemoryDerivation) -> Option<(LoadKind, &MachineTerm)> {
    let MemoryDerivation::Store { value, .. } = step else {
        return None;
    };
    match value.native() {
        ProgramValue::Int8(bits) => Some((LoadKind::Int8, bits)),
        ProgramValue::UInt8(bits) => Some((LoadKind::UInt8, bits)),
        ProgramValue::Int16(bits) => Some((LoadKind::Int16, bits)),
        ProgramValue::UInt16(bits) => Some((LoadKind::UInt16, bits)),
        ProgramValue::Int32(bits) => Some((LoadKind::Int32, bits)),
        ProgramValue::UInt32(bits) => Some((LoadKind::UInt32, bits)),
        ProgramValue::Int64(bits) | ProgramValue::UInt64(bits) => Some((LoadKind::Bits64, bits)),
        ProgramValue::Int128(bits) => Some((LoadKind::Int128, bits)),
        ProgramValue::UInt128(bits) => Some((LoadKind::UInt128, bits)),
        _ => None,
    }
}

impl PartialEq for PathLink {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for PathLink {}

impl std::hash::Hash for PathLink {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for PathLink {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PathLink {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

/// A program point: a node a proof path reached, which Surface names with
/// `at(point, ...)`. A memory read is lowered to its version point, the point
/// back to which the recorded steps show the cell unchanged, and holds that
/// point.
///
/// Exact reads and indexed reads include the point they name in the term key.
/// Legacy reads still use the interned memory as their key.
#[derive(Clone)]
pub struct ProgramPoint {
    memory: SharedMemory,
    path: PathLink,
    read: ReadSelection,
}

#[derive(Clone)]
enum ReadSelection {
    Legacy,
    Exact,
    Entry,
    CallOutput,
    IndexedWrite(Arc<MemoryDerivation>),
}

impl std::fmt::Debug for ProgramPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut point = f.debug_struct("ProgramPoint");
        if let Some(version) = self.read_version_id() {
            point.field("version", &version);
        } else {
            point
                .field("memory", &self.memory)
                .field("path", &self.path);
        }
        point.finish()
    }
}

type PendingPointKey = (Option<ProgramPointId>, usize, (u32, u32), bool);

thread_local! {
    /// The point made for each pending step log, so a state asked for its
    /// point twice gets one point. Keyed by the log object, not by memory
    /// contents: two routes to equal memory are two logs and two points.
    /// The entry holds the log, so its address is not reused while keyed.
    /// The same pending log may be reached from a view with different
    /// evidence that its first indexed store follows the execution point.
    static PENDING_POINTS: std::cell::RefCell<
        std::collections::HashMap<PendingPointKey, (Arc<StepLog>, PathLink)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The point after `path` that the steps in `steps` reach, with `memory`.
fn pending_point(path: &PathLink, steps: &Arc<StepLog>, memory: &SharedMemory) -> PathLink {
    let continues_index = steps.previous.is_none() && path.matches_indexed_view(steps.step.base());
    let key = (
        path.id(),
        Arc::as_ptr(steps) as usize,
        memory.arena_id(),
        continues_index,
    );
    PENDING_POINTS.with(|points| {
        points
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| {
                (
                    steps.clone(),
                    path.after_with_index(
                        memory.clone(),
                        Some(steps.clone()),
                        PointTransition::Provisional,
                    ),
                )
            })
            .1
            .clone()
    })
}

/// Identity of a read, separate from the memory view retained for checking.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(in crate::kernel) enum ReadKey {
    Memory((u32, u32)),
    Point(ProgramPointId),
    /// A rewritten or unverified view has no evidence it still names the
    /// recorded bytes. Keep its explicit view in the key.
    View(ProgramPointId, (u32, u32)),
}

impl PartialEq for ProgramPoint {
    fn eq(&self, other: &Self) -> bool {
        match (self.read_version_id(), other.read_version_id()) {
            (None, None) => self.memory == other.memory,
            _ => self.read_key() == other.read_key(),
        }
    }
}

impl Eq for ProgramPoint {}

impl std::hash::Hash for ProgramPoint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if self.read_version_id().is_some() {
            self.read_key().hash(state);
        } else {
            self.memory.hash(state);
        }
    }
}

impl PartialOrd for ProgramPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProgramPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self.read_version_id(), other.read_version_id()) {
            (None, None) => self.memory.cmp(&other.memory),
            _ => self.read_key().cmp(&other.read_key()),
        }
    }
}

impl ProgramPoint {
    /// A point built from a bare memory state, with no place on a path.
    pub fn at(memory: &SharedMemory) -> Self {
        Self {
            memory: memory.clone(),
            path: PathLink::default(),
            read: ReadSelection::Legacy,
        }
    }

    /// The point a `SymbolicMemory` value stands at, interning it first. Callers
    /// that already hold an interned state use [`ProgramPoint::at`].
    pub(crate) fn of_memory(memory: &SymbolicMemory) -> Self {
        Self::at(&intern_memory(memory.clone()))
    }

    /// The first point of a new path, standing at `memory`: a place no other
    /// point leads to, such as the memory a pure theorem quantifies over. Unlike
    /// [`ProgramPoint::of_memory`], the point has a place on a path, so reads
    /// there can be followed back along it.
    pub(crate) fn starting_at(memory: &SymbolicMemory) -> Self {
        let shared = intern_memory_ref(memory);
        let path = PathLink::default().after(shared.clone(), memory.pending_steps.clone());
        Self {
            memory: shared,
            path,
            read: ReadSelection::Legacy,
        }
    }

    /// The point a state stands at on its path.
    #[cfg_attr(not(test), allow(dead_code))]
    /// The point a state with `memory` stands at, `path` being the last
    /// point it reached. Steps the state has taken since, still in the
    /// memory's log, are a point of their own after that one, so the point
    /// handed out holds the memory it names. The log determines the
    /// successor even when the steps return to the predecessor's contents.
    pub(super) fn of_state(memory: &SymbolicMemory, path: &PathLink) -> Self {
        let shared = intern_memory_ref(memory);
        let path = match &memory.pending_steps {
            Some(steps) => pending_point(path, steps, &shared),
            _ => path.clone(),
        };
        Self {
            memory: shared,
            path,
            read: ReadSelection::Legacy,
        }
    }

    pub(crate) fn shared_memory(&self) -> &SharedMemory {
        &self.memory
    }

    /// This point with its memory's values renamed: the same place on the
    /// path, its memory spelled with substituted variables.
    pub(crate) fn with_renamed_memory(&self, memory: SharedMemory) -> Self {
        Self {
            memory,
            path: self.path.clone(),
            read: self.read.clone(),
        }
    }

    /// Where on its path this point is.
    pub(super) fn path_link(&self) -> &PathLink {
        &self.path
    }

    /// The interned memory state this point stands for, by value.
    pub(crate) fn into_shared_memory(self) -> SharedMemory {
        self.memory
    }

    pub(crate) fn memory(&self) -> &SymbolicMemory {
        self.memory.memory()
    }

    /// This point's identity on its path, or none for a point built from a
    /// bare memory state.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn id(&self) -> Option<ProgramPointId> {
        self.path.id()
    }

    /// The point in a read's key, whether selected exactly or as a version.
    pub(crate) fn read_version_id(&self) -> Option<ProgramPointId> {
        if !matches!(self.read, ReadSelection::Legacy) {
            self.id()
        } else {
            None
        }
    }

    pub(in crate::kernel) fn read_key(&self) -> ReadKey {
        match self.read_version_id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.arena_id()),
        }
    }

    /// Read applications use the execution version when known. Legacy views
    /// retain their existing read identity across pure memory materialization.
    pub(in crate::kernel) fn congruence_read_key(&self) -> ReadKey {
        match self.read_version_id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.read_identity()),
        }
    }

    pub(in crate::kernel) fn observation_key(&self) -> ReadKey {
        match self.id() {
            Some(id) => self.read_key_at(id),
            None => ReadKey::Memory(self.memory.arena_id()),
        }
    }

    fn read_key_at(&self, id: ProgramPointId) -> ReadKey {
        if self.path.matches_indexed_view(&self.memory) {
            ReadKey::Point(id)
        } else {
            ReadKey::View(id, self.memory.arena_id())
        }
    }

    pub(crate) fn names_exact_read(&self, read: &Self) -> bool {
        self.id()
            .is_some_and(|id| self.read_key_at(id) == read.read_key())
    }

    /// An exact read keeps the selected point even if another point has equal
    /// memory or supplies the cell's ordinary version.
    pub(in crate::kernel) fn for_exact_read(mut self) -> Self {
        self.read = ReadSelection::Exact;
        self
    }

    /// The same view identified by its memory, as an unselected point is.
    /// Reads through it still use the recorded path's cell versions.
    pub(in crate::kernel) fn for_legacy_read(mut self) -> Self {
        self.read = ReadSelection::Legacy;
        self
    }

    pub(crate) fn is_exact_read(&self) -> bool {
        matches!(self.read, ReadSelection::Exact) && self.id().is_some()
    }

    /// Skip the recorded suffix that is already known to leave the entire
    /// parameter storage alone. An unverified view cannot use the suffix.
    pub(in crate::kernel) fn parameter_read_start(&self, block: &AddressBase) -> Self {
        if !external_storage(block) {
            return self.clone();
        }
        let anchor = self
            .path
            .0
            .as_ref()
            .filter(|_| self.path.matches_indexed_view(&self.memory))
            .and_then(|point| point.external_read_start.as_ref());
        if let Some(anchor) = anchor
            && let Some(point) = anchor.point.upgrade()
        {
            return Self {
                memory: anchor.memory.clone(),
                path: PathLink(Some(point), anchor.view.clone()),
                read: ReadSelection::Legacy,
            };
        }
        self.clone()
    }

    /// A function-entry array version reached through a recorded suffix of
    /// local operations and checked calls that preserve parameter storage.
    pub(in crate::kernel) fn entry_array_version(&self, block: &AddressBase) -> Option<Self> {
        if !external_storage(block) {
            return None;
        }
        let entry = external_array_entry(&self.path, &self.memory)?;
        Some(Self {
            memory: entry.memory,
            path: PathLink(Some(entry.point.upgrade()?), entry.view),
            read: ReadSelection::Exact,
        })
    }

    /// A scalar supplied by the caller can have a version even when no
    /// store supplies a value. Use the recorded disjoint suffix only when
    /// it reaches a verified function-entry view.
    pub(crate) fn entry_integer_version(&self, pointer: &Address, kind: LoadKind) -> Option<Self> {
        if kind != LoadKind::Int32 {
            return None;
        }
        self.external_entry_read(pointer)
    }

    pub(crate) fn generic_entry_version(
        &self,
        pointer: &Address,
        parameter: super::TypeParameterName,
    ) -> Option<Self> {
        if parameter.is_enum() {
            return None;
        }
        self.external_entry_read(pointer)
    }

    fn external_entry_read(&self, pointer: &Address) -> Option<Self> {
        if pointer.base != AddressBase::ExternalArgument {
            return None;
        }
        let mut entry = self.parameter_read_start(&pointer.base);
        let node = entry.path.0.as_ref()?;
        // The empty view has no previously materialized values to account
        // for when selecting the version of a substituted address.
        if !node.function_entry
            || !entry.path.matches_indexed_view(&entry.memory)
            || entry.memory() != &SymbolicMemory::default()
        {
            return None;
        }
        entry.read = ReadSelection::Entry;
        Some(entry)
    }

    pub(in crate::kernel) fn is_entry_read(&self) -> bool {
        matches!(self.read, ReadSelection::Entry) && self.path.matches_indexed_view(&self.memory)
    }

    /// A rewritten address keeps this entry only when ordinary lowering can
    /// select it for the new cell too.
    pub(in crate::kernel) fn entry_version_after_rewrite(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        if self.is_entry_read() {
            self.entry_integer_version(pointer, kind)
        } else {
            None
        }
    }

    pub(crate) fn ordinary_typed_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        self.indexed_typed_version(pointer, value_type)
            .or_else(|| match value_type {
                ProgramType::Int32 => self
                    .call_output_integer_version(pointer, LoadKind::Int32)
                    .or_else(|| self.entry_integer_version(pointer, LoadKind::Int32)),
                ProgramType::Parameter(parameter) => self.generic_entry_version(pointer, parameter),
                _ => None,
            })
    }

    pub(in crate::kernel) fn supports_local_call_word(pointer: &Address) -> bool {
        indexed_local(&pointer.base) && pointer.offset == AddressOffset::Constant(0)
    }

    pub(in crate::kernel) fn call_output_integer_version(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        if kind != LoadKind::Int32 || !Self::supports_local_call_word(pointer) {
            return None;
        }
        self.indexed_version(pointer, kind.byte_width(), |effect| {
            matches!(
                effect,
                MemoryDerivation::ObjectInitializationRecorded {
                    call_word: true,
                    ..
                }
            )
        })
    }

    pub(crate) fn supports_indexed_version(pointer: &Address) -> bool {
        read_bucket(&pointer.base).is_some()
    }

    /// A direct integer cell's version, if this path has a recorded direct write
    /// and the transitions after it preserve the object by construction.
    pub(crate) fn indexed_integer_version(
        &self,
        pointer: &Address,
        kind: LoadKind,
    ) -> Option<Self> {
        self.indexed_version(pointer, kind.byte_width(), |store| {
            integer_store_bits(store).is_some_and(|(stored_kind, _)| stored_kind == kind)
        })
    }

    pub(crate) fn indexed_typed_version(
        &self,
        pointer: &Address,
        value_type: ProgramType,
    ) -> Option<Self> {
        if value_type == ProgramType::Bool || value_type.is_pointer() {
            return self.indexed_version(pointer, value_type.byte_width(), |store| {
                matches!(store, MemoryDerivation::Store { value, .. } if value.program_type() == value_type)
            });
        }
        self.indexed_integer_version(pointer, LoadKind::of_type(value_type)?)
    }

    pub(super) fn abstract_local_version(
        &self,
        pointer: &Address,
        parameter: super::TypeParameterName,
    ) -> Option<Self> {
        if !indexed_local(&pointer.base) || pointer.offset != AddressOffset::Constant(0) {
            return None;
        }
        self.indexed_version(pointer, super::ABSTRACT_VALUE_WIDTH, |store| {
            matches!(store, MemoryDerivation::Store { value, .. }
                if value.program_type() == ProgramType::Parameter(parameter))
        })
    }

    fn indexed_version(
        &self,
        pointer: &Address,
        bytes: u32,
        matches_source: impl FnOnce(&MemoryDerivation) -> bool,
    ) -> Option<Self> {
        let bucket = read_bucket(&pointer.base)?;
        let node = self.path.0.as_ref()?;
        if !self.path.matches_indexed_view(&self.memory) {
            return None;
        }
        let (anchor, start) = read_displacement(&pointer.offset)?;
        let end = start.checked_add(i64::from(bytes))?;
        let block = node.point_read_index.blocks.get(bucket)?;
        if block.origin != read_origin(pointer, anchor) {
            return None;
        }
        let write = block.cells.get(&start)?;
        if write.end != end || !matches_source(&write.source) {
            return None;
        }
        let version = write.version.upgrade()?;
        Some(Self {
            memory: version.memory.clone(),
            path: PathLink(Some(version), IndexedView::Recorded),
            read: if matches!(
                write.source.as_ref(),
                MemoryDerivation::ObjectInitializationRecorded {
                    call_word: true,
                    ..
                }
            ) {
                ReadSelection::CallOutput
            } else {
                ReadSelection::IndexedWrite(write.source.clone())
            },
        })
    }

    /// The recorded value of this indexed read's defining store.
    pub(crate) fn indexed_integer_store_bits(&self) -> Option<&MachineTerm> {
        integer_store_bits(self.indexed_write()?).map(|(_, bits)| bits)
    }

    pub(in crate::kernel) fn indexed_stored_value(&self) -> Option<&StoredMemoryValue> {
        let MemoryDerivation::Store { value, .. } = self.indexed_write()? else {
            return None;
        };
        Some(value)
    }

    fn indexed_write(&self) -> Option<&MemoryDerivation> {
        match &self.read {
            ReadSelection::IndexedWrite(store) if self.path.matches_indexed_view(&self.memory) => {
                Some(store)
            }
            _ => None,
        }
    }

    /// The identities of the points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessor_ids(&self) -> Vec<ProgramPointId> {
        self.path.predecessor_ids()
    }

    /// True when this point is later in the recorded history than `other`.
    /// SymbolicMemory state ids strictly increase along derivation edges, so comparing
    /// them orders two points of one arena without walking.
    pub(crate) fn is_later_than(&self, other: &Self) -> bool {
        let (arena, id) = self.memory.arena_id();
        let (other_arena, other_id) = other.memory.arena_id();
        arena == other_arena && id > other_id
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::PathLink;

    fn memory_holding(value: u32) -> SymbolicMemory {
        let block: AddressBase = "local:slot".into();
        let slot = Address {
            base: block.clone(),
            offset: AddressOffset::Constant(0),
        };
        SymbolicMemory::new()
            .with_block(block, 4)
            .store(slot, ProgramValue::Int32(MachineTerm::constant(value)))
    }

    fn slot() -> Address {
        Address {
            base: "local:slot".into(),
            offset: AddressOffset::Constant(0),
        }
    }

    fn stored(state: &ExecutionState, value: u32) -> ExecutionState {
        let memory = state
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(value)));
        state.clone().with_memory(memory)
    }

    /// Two paths store different values and then the same one, so they end
    /// in one interned memory, whose arena history is the first path's. Each
    /// final point still holds the store its own path made, from its own
    /// predecessor's memory.
    #[test]
    fn each_point_holds_the_steps_its_own_path_took() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left_mid = stored(&start, 1);
        let right_mid = stored(&start, 2);
        let left = stored(&left_mid, 3);
        let right = stored(&right_mid, 3);
        assert_eq!(left.program_point(), right.program_point());

        let base_of_only_step = |state: &ExecutionState| {
            let steps = state.path_link().steps().expect("a store is a step");
            let mut steps = steps.newest_first();
            let (step, produced) = steps.next().unwrap();
            assert!(steps.next().is_none());
            assert_eq!(produced, state.program_point().shared_memory());
            step.base().clone()
        };
        assert_eq!(
            base_of_only_step(&left),
            *left_mid.program_point().shared_memory()
        );
        assert_eq!(
            base_of_only_step(&right),
            *right_mid.program_point().shared_memory()
        );
        assert!(left.memory().pending_steps.is_none());
    }

    /// A state set up by steps before its first point begins at the memory
    /// those steps started from, so a walk back can cross them.
    #[test]
    fn a_path_begins_before_its_first_steps() {
        let state = ExecutionState::default().with_memory(memory_holding(0));
        let point = state.program_point();
        let [start] = point.path_link().predecessors() else {
            panic!("the first point follows the path's start");
        };
        assert!(start.predecessors().is_empty());
        assert_eq!(start.memory(), Some(&intern_memory(SymbolicMemory::new())));
    }

    /// A point that starts a path has an identity even when no step reached
    /// its memory.
    #[test]
    fn a_starting_point_has_a_place_on_a_path() {
        let point = ProgramPoint::starting_at(&SymbolicMemory::new());
        assert!(point.id().is_some());
        assert!(
            ProgramPoint::of_memory(&SymbolicMemory::new())
                .id()
                .is_none()
        );
    }

    /// A join records where its arms split.
    #[test]
    fn a_join_records_where_its_arms_split() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left = stored(&start, 1);
        let right = stored(&start, 1);
        let mut joined = left.clone();
        joined.join_program_points(&left, &right, start.path_link());
        assert_eq!(
            joined.path_link().split().and_then(PathLink::id),
            start.program_point().id()
        );
    }

    #[test]
    fn an_entry_read_names_its_point_without_a_store_receipt() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let other_entry = ExecutionState::new().begin_function_entry_memory();
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let select = |state: &ExecutionState| {
            state
                .program_point()
                .ordinary_typed_version(&pointer, ProgramType::Int32)
        };
        let version = select(&entry).expect("an ordinary entry version");
        assert_eq!(version.read_version_id(), entry.program_point().id());
        assert!(version.indexed_integer_store_bits().is_none());
        assert!(
            entry
                .program_point()
                .ordinary_typed_version(&pointer, ProgramType::Int32Pointer)
                .is_none()
        );
        assert_ne!(select(&other_entry).unwrap(), version);

        let declared = entry
            .clone()
            .with_memory(entry.memory().clone().with_block("local:slot", 4));
        let after_local_store = stored(&declared, 3);
        assert_eq!(select(&after_local_store), Some(version.clone()));
        let exact = after_local_store.program_point().for_exact_read();
        assert!(exact.is_exact_read());
        assert_ne!(exact, version);

        let overwritten =
            after_local_store
                .clone()
                .with_memory(after_local_store.memory().clone().store(
                    pointer.clone(),
                    ProgramValue::Int32(MachineTerm::constant(7)),
                ));
        let new_version = select(&overwritten).expect("the defining store is indexed");
        assert_ne!(new_version, version);
        assert_eq!(
            new_version.indexed_integer_store_bits(),
            Some(&MachineTerm::constant(7))
        );
    }

    #[test]
    fn a_join_retains_the_common_external_entry() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let declared = entry
            .clone()
            .with_memory(entry.memory().clone().with_block(slot().base, 4));
        let first = stored(&declared, 1);
        let second = stored(&declared, 2);
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(4),
        };
        let join = |left: &ExecutionState, right: &ExecutionState| {
            let mut joined = left.clone();
            joined.join_program_points(left, right, declared.path_link());
            joined.program_point()
        };
        let entry_id = entry.program_point().id();
        assert_eq!(
            join(&first, &second)
                .entry_integer_version(&pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id()),
            entry_id,
        );

        let changed = second.clone().with_memory(second.memory().clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(3)),
        ));
        assert!(
            join(&first, &changed)
                .entry_integer_version(&pointer, LoadKind::Int32)
                .is_none()
        );
    }

    #[test]
    fn fixed_offset_versions_match_the_path_and_stop_at_overlaps_or_log_gaps() {
        let _session = crate::kernel::VerificationSession::enter();
        let left = slot();
        let right = left.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(left.base.clone(), 8));
        let store_word = |state: &ExecutionState, address: Address, bits| {
            state.clone().with_memory(
                state
                    .memory()
                    .clone()
                    .store(address, ProgramValue::Int32(MachineTerm::constant(bits))),
            )
        };
        let written = store_word(&start, right.clone(), 7);
        let sibling = store_word(&written, left.clone(), 1);
        let version = |state: &ExecutionState| {
            state
                .program_point()
                .indexed_integer_version(&right, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let walked =
            crate::kernel::resource_tracker::cell_version_on_path(sibling.path_link(), &right, 4);
        assert_eq!(
            walked.and_then(|point| point.id()),
            written.program_point_id()
        );
        assert_eq!(version(&sibling), written.program_point_id());

        let overlapping = store_word(&sibling, left.offset_by_bytes(2), 0);
        assert_eq!(version(&overlapping), None);
        let byte = ProgramValue::UInt8(MachineTerm::narrow_constant(MachineIntegerType::UInt8, 0));
        let middle_byte = sibling.clone().with_memory(
            sibling
                .memory()
                .clone()
                .store(right.offset_by_bytes(1), byte),
        );
        assert_eq!(version(&middle_byte), None);
        assert_eq!(version(&sibling), written.program_point_id());

        let replacement = sibling
            .memory()
            .clone()
            .store(right.clone(), ProgramValue::Int32(MachineTerm::constant(9)));
        let unlogged = sibling
            .clone()
            .with_materialized_memory_at_current_point(replacement);
        assert_eq!(unlogged.program_point_id(), sibling.program_point_id());
        assert_eq!(version(&unlogged), None);
        assert_eq!(version(&store_word(&unlogged, left, 2)), None);
    }

    #[test]
    fn a_join_keeps_the_shared_store_and_declines_a_same_value_rewrite() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let other = slot.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 8));
        let split = stored(&start, 7);
        let write_sibling = |value| {
            split.clone().with_memory(split.memory().clone().store(
                other.clone(),
                ProgramValue::Int32(MachineTerm::constant(value)),
            ))
        };
        let left = write_sibling(2);
        let right = write_sibling(3);
        let mut joined = left.clone();
        joined.join_program_points(&left, &right, split.path_link());
        let version = |state: &ExecutionState, pointer: &Address| {
            state
                .program_point()
                .indexed_integer_version(pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        assert_eq!(version(&joined, &slot), split.program_point_id());
        let walked =
            crate::kernel::resource_tracker::cell_version_on_path(joined.path_link(), &slot, 4);
        assert_eq!(
            walked.and_then(|point| point.id()),
            split.program_point_id()
        );
        assert_eq!(version(&joined, &other), None);

        let rewritten = stored(&left, 7);
        assert_eq!(rewritten.memory(), left.memory());
        joined.join_program_points(&left, &rewritten, split.path_link());
        assert_eq!(version(&joined, &slot), None);
    }

    #[test]
    fn checked_call_and_loop_footprints_keep_the_other_object_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = slot();
        let other = Address {
            base: "local:other".into(),
            offset: AddressOffset::Constant(0),
        };
        let start = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block(slot.base.clone(), 4)
                .with_block(other.base.clone(), 4),
        );
        let written = stored(&start, 7);
        let written = written.clone().with_memory(
            written
                .memory()
                .clone()
                .store(other.clone(), ProgramValue::Int32(MachineTerm::constant(2))),
        );
        let version = |state: &ExecutionState, pointer: &Address| {
            state
                .program_point()
                .indexed_integer_version(pointer, LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let expected = version(&written, &slot);
        assert!(expected.is_some());
        let range = MemoryRange::new(other.clone(), 0.into(), 1.into());
        let called =
            written
                .clone()
                .with_memory(written.memory().clone().with_storage_memory_havoc(
                    Variable(38_131),
                    std::slice::from_ref(&range),
                    &PureFactContext::new(),
                ));
        assert_eq!(version(&called, &slot), expected);
        assert_eq!(version(&called, &other), None);
        let unknown =
            called
                .clone()
                .with_memory(called.memory().clone().with_storage_memory_havoc(
                    Variable(38_132),
                    &[MemoryRange::unnamed_footprint()],
                    &PureFactContext::new(),
                ));
        assert_eq!(version(&unknown, &slot), None);

        let mut head = written.clone();
        head.replace_loop_head_local_cell(
            other.clone(),
            ProgramValue::Int32(MachineTerm::constant(3)),
        );
        let memory = head
            .memory()
            .clone()
            .with_loop_memory_havoc_preserving_loans(
                Variable(38_133),
                &std::collections::BTreeSet::new(),
                Some(&[range]),
                None,
            );
        head.set_loop_head_memory(memory);
        assert_ne!(head.program_point_id(), written.program_point_id());
        assert_eq!(version(&head, &slot), expected);
        assert_eq!(version(&head, &other), None);
        let mut exit = head.clone();
        exit.join_loop_exit_program_points(&[&head]);
        assert_ne!(exit.program_point_id(), head.program_point_id());
        assert_eq!(version(&exit, &slot), expected);
        let rewritten = stored(&head, 7);
        exit.join_loop_exit_program_points(&[&head, &rewritten]);
        assert_eq!(version(&exit, &slot), None);
    }

    #[test]
    fn an_overlapping_write_or_a_log_gap_ends_the_earlier_batch_version() {
        let _session = crate::kernel::VerificationSession::enter();
        let first = slot();
        let second = first.offset_by_bytes(4);
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(first.base.clone(), 8));
        let store = |place, value| (place, ProgramValue::Int32(MachineTerm::constant(value)));
        let (address, value) = store(first.clone(), 7);
        let initial = start.memory().clone().store(address, value);
        let (address, value) = store(second.clone(), 8);
        let batch = initial.clone().store(address, value);
        let kind = LoadKind::Int32;
        let version = |state: &ExecutionState, place: &Address| {
            state.program_point().indexed_integer_version(place, kind)
        };
        let overlap = start.clone().with_memory(batch.store(
            first.offset_by_bytes(2),
            ProgramValue::UInt8(MachineTerm::narrow_constant(MachineIntegerType::UInt8, 0)),
        ));
        assert!(version(&overlap, &first).is_none());
        assert_eq!(
            version(&overlap, &second)
                .unwrap()
                .indexed_integer_store_bits(),
            Some(&MachineTerm::constant(8))
        );

        let gap = initial.with_uninitialized_object(Address::symbolic(Variable(38_130)), 4);
        let (address, value) = store(second, 9);
        let detached = start.with_memory(gap.store(address, value));
        assert!(version(&detached, &first).is_none());
    }

    #[test]
    fn named_cell_views_retain_logged_versions_without_reading_their_suffix() {
        let _session = crate::kernel::VerificationSession::enter();
        let start =
            ExecutionState::new().with_memory(SymbolicMemory::new().with_block("local:slot", 4));
        let written = stored(&start, 7);
        let version = |state: &ExecutionState| {
            state
                .program_point()
                .indexed_integer_version(&slot(), LoadKind::Int32)
                .and_then(|point| point.read_version_id())
        };
        let mut work = Vec::new();
        for count in [4, 64, 1024] {
            let mut memory = written.memory().clone();
            let external = Address::symbolic(Variable(38_127));
            for index in 0..count {
                memory = memory.materialize_named_cell(
                    external.offset_by_bytes(4 * index),
                    ProgramValue::Int32(MachineTerm::constant(index)),
                );
            }
            let (named, used) = crate::instrumentation::measure_deterministic_work(|| {
                written
                    .clone()
                    .with_materialized_memory_at_current_point(memory)
            });
            assert_eq!(named.program_point_id(), written.program_point_id());
            assert_eq!(version(&named), written.program_point_id());
            assert!(named.memory().pending_steps.is_none());
            work.push(used);
        }
        assert!(work.iter().all(|&used| used <= work[0] + 64), "{work:?}");

        // The source itself can still be carrying its own actual store.
        let pending = start.clone().with_materialized_memory(
            start
                .memory()
                .clone()
                .store(slot(), ProgramValue::Int32(MachineTerm::constant(11))),
        );
        let point = pending.program_point().id();
        let named = pending.clone().with_materialized_memory_at_current_point(
            pending.memory().clone().materialize_named_cell(
                Address::symbolic(Variable(38_128)),
                ProgramValue::Int32(MachineTerm::constant(42)),
            ),
        );
        assert_eq!(version(&named), point);

        // A replacement whose log performed a real store cannot carry the
        // old version even when it writes the same value to the same cell.
        let same_contents = written
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(7)));
        assert_eq!(&same_contents, written.memory());
        let rejected = written
            .clone()
            .with_materialized_memory_at_current_point(same_contents.clone());
        assert_eq!(version(&rejected), None);
        let next = written
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(13)));
        let indexed = written.clone().with_materialized_memory(next.clone());
        assert_eq!(version(&indexed), indexed.program_point().id());
        assert_eq!(version(&rejected.with_materialized_memory(next)), None);
        let unlogged = written.clone().with_materialized_memory_at_current_point(
            same_contents.materialize_named_cell(
                Address::symbolic(Variable(38_129)),
                ProgramValue::Int32(MachineTerm::constant(99)),
            ),
        );
        assert_eq!(version(&unlogged), None);
    }

    #[test]
    fn entry_memory_views_share_one_root_before_the_first_execution_store() {
        let _session = crate::kernel::VerificationSession::enter();
        let entry = ExecutionState::new().begin_function_entry_memory();
        let root = entry.program_point_id().unwrap();
        let slot = slot();
        let declared = entry
            .clone()
            .with_function_entry_memory(entry.memory().clone().with_block(slot.base.clone(), 4));
        let initialized = declared.clone().with_function_entry_memory(
            declared
                .memory()
                .clone()
                .store(slot.clone(), ProgramValue::Int32(MachineTerm::constant(7))),
        );
        for view in [&declared, &initialized] {
            assert_eq!(view.observation_point_id(), Some(root));
            assert!(view.path_link().steps().is_none());
            assert!(view.path_link().predecessors().is_empty());
        }
        let executed = stored(&initialized, 9);
        assert_eq!(executed.path_link().predecessor_ids(), vec![root]);
        assert_ne!(executed.program_point_id(), Some(root));
        assert_eq!(
            executed
                .program_point()
                .indexed_integer_version(&slot, LoadKind::Int32)
                .and_then(|point| point.read_version_id()),
            executed.program_point_id(),
        );
    }

    /// The arena's stored instance carries no path's steps.
    #[test]
    fn the_arena_keeps_no_steps() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let memory = start
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(5)));
        assert!(memory.pending_steps.is_some());
        assert!(intern_memory_ref(&memory).memory().pending_steps.is_none());
    }

    /// A state that has taken steps since its last point stands at a point
    /// after them, holding its current memory; a frame built from the state
    /// stands there too, with the state's own memory value.
    #[test]
    fn a_state_with_pending_steps_stands_after_them() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let moved = start.clone().with_materialized_memory(
            start
                .memory()
                .clone()
                .store(slot(), ProgramValue::Int32(MachineTerm::constant(7))),
        );
        let point = moved.program_point();
        assert_ne!(point.id(), start.program_point().id());
        assert_eq!(
            point.predecessor_ids(),
            vec![start.program_point().id().unwrap()]
        );
        assert_eq!(point.path_link().memory(), Some(point.shared_memory()));

        let frame = ExecutionState::at_state(&moved);
        assert_eq!(frame.program_point().id(), point.id());
        assert!(frame.memory().same_storage_roots(moved.memory()));
    }

    /// Recorded steps reach a new point even when their net contents match
    /// the predecessor. Looking up that pending successor, or making a frame
    /// there, must retain the same point identity.
    #[test]
    fn pending_steps_returning_to_equal_memory_reach_a_stable_successor() {
        let _session = crate::kernel::VerificationSession::enter();
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let memory = start
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(1)))
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(0)));
        assert!(memory.pending_steps.is_some());
        let moved = start.clone().with_materialized_memory(memory);
        assert_eq!(start.memory(), moved.memory());
        let point = moved.program_point();
        assert_ne!(point.id(), start.program_point().id());
        assert_eq!(
            point.predecessor_ids(),
            vec![start.program_point().id().unwrap()]
        );
        assert_eq!(moved.program_point().id(), point.id());
        assert_eq!(point.path_link().memory(), Some(point.shared_memory()));
        let frame = ExecutionState::at_state(&moved);
        assert_eq!(frame.program_point().id(), point.id());
        assert!(frame.memory().pending_steps.is_none());
        assert_eq!(frame.program_point().id(), point.id());
        // A frame without pending steps stays at the predecessor.
        assert_eq!(
            ExecutionState::at_state(&start).program_point().id(),
            start.program_point().id()
        );
    }

    /// A state that takes another state's memory continues that state's
    /// path, through the steps that made the memory, not its own.
    #[test]
    fn taking_another_states_memory_continues_its_path() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let elsewhere = stored(&start, 1);
        let taken = elsewhere
            .memory()
            .clone()
            .store(slot(), ProgramValue::Int32(MachineTerm::constant(2)));
        let mut here = start.clone();
        here.set_memory_continuing(&elsewhere, taken);
        assert_eq!(
            here.program_point().predecessor_ids(),
            vec![elsewhere.program_point().id().unwrap()]
        );
        assert!(here.path_link().steps().is_some());

        let mut same = start.clone();
        same.set_memory_of(&elsewhere);
        assert_eq!(same.program_point().id(), elsewhere.program_point().id());
    }

    /// A path is a chain of points; dropping a long one must not recurse
    /// once per link.
    #[test]
    fn a_long_path_drops_without_recursing_per_point() {
        let memory = intern_memory(SymbolicMemory::new());
        let mut point = PathLink::default();
        for _ in 0..200_000 {
            point = point.after(memory.clone(), None);
        }
        drop(point);
    }

    /// Two paths that write different values and then the same one end in
    /// equal states, as two `return`s that each end their locals' lifetimes
    /// do. They are still two points, each reached from its own path.
    #[test]
    fn two_paths_to_equal_memory_reach_two_points() {
        let start = ExecutionState::default().with_memory(memory_holding(0));
        let left_mid = start.clone().with_memory(memory_holding(1));
        let right_mid = start.clone().with_memory(memory_holding(2));
        let left = left_mid.clone().with_memory(memory_holding(3));
        let right = right_mid.clone().with_memory(memory_holding(3));

        assert_eq!(left, right);
        assert_eq!(left.program_point(), right.program_point());
        assert_ne!(left.program_point().id(), right.program_point().id());
        assert_eq!(
            left.program_point().predecessor_ids(),
            vec![left_mid.program_point().id().unwrap()]
        );
        assert_eq!(
            right.program_point().predecessor_ids(),
            vec![right_mid.program_point().id().unwrap()]
        );

        let mut joined = left.clone();
        joined.join_program_points(&left, &right, start.path_link());
        assert_eq!(
            joined.program_point().predecessor_ids(),
            vec![
                left.program_point().id().unwrap(),
                right.program_point().id().unwrap()
            ]
        );
    }
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/program_point.rs");
    }
}
