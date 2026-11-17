//! The program point: a node a proof path reached.
//!
//! A [`ProgramPoint`] carries the memory state there and its place on the
//! path: an identity minted at each memory transition, linked to the point or
//! points it was reached from. Memory states are interned by content, so two
//! paths that reach equal memory share one state; their points are still two.
//!
//! Surface records the name of each point it records a state at
//! (`RecordedStates::point_name`).

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use super::{Memory, MemoryDerivation, SharedMemory, intern_memory, intern_memory_ref};

/// The identity of one point an execution path reached.
///
/// Identities are unique within a process and carry no order: no decision
/// may depend on comparing two of them other than for equality.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct ProgramPointId(u64);

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
}

impl StepLog {
    /// `previous` with `step`, which produced `produced`, added as newest.
    pub(crate) fn push(
        previous: Option<Arc<Self>>,
        step: Arc<MemoryDerivation>,
        produced: SharedMemory,
    ) -> Arc<Self> {
        Arc::new(Self {
            step,
            produced,
            previous,
        })
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

#[derive(Debug)]
struct PointNode {
    id: ProgramPointId,
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
}

impl Drop for PointNode {
    /// A long path is a long chain; dropping it one link at a time keeps the
    /// stack flat however many transitions the path made.
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.predecessors).into_vec();
        pending.extend(self.split.take());
        while let Some(PathLink(node)) = pending.pop() {
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
pub(crate) struct PathLink(Option<Arc<PointNode>>);

impl PathLink {
    /// A new point reached from this one by `steps`, where the path has
    /// `memory`.
    pub(crate) fn after(&self, memory: SharedMemory, steps: Option<Arc<StepLog>>) -> Self {
        Self::reached_from(memory, steps, Box::new([self.clone()]), None)
    }

    /// A new point where two arms that split at `split` rejoin with
    /// `memory`.
    pub(crate) fn joining(left: &Self, right: &Self, split: &Self, memory: SharedMemory) -> Self {
        Self::reached_from(
            memory,
            None,
            Box::new([left.clone(), right.clone()]),
            Some(split.clone()),
        )
    }

    fn reached_from(
        memory: SharedMemory,
        steps: Option<Arc<StepLog>>,
        predecessors: Box<[PathLink]>,
        split: Option<PathLink>,
    ) -> Self {
        let predecessors = predecessors
            .into_vec()
            .into_iter()
            .filter(|point| point.0.is_some())
            .collect();
        Self(Some(Arc::new(PointNode {
            id: ProgramPointId::fresh(),
            memory,
            steps,
            predecessors,
            split: split.filter(|point| point.0.is_some()),
        })))
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
/// For now two points compare, hash and order by the interned memory state
/// there; the path identity is carried but not yet compared. That is an
/// implementation detail callers must not rely on.
#[derive(Clone, Debug)]
pub struct ProgramPoint {
    memory: SharedMemory,
    path: PathLink,
}

thread_local! {
    /// The point made for each pending step log, so a state asked for its
    /// point twice gets one point. Keyed by the log object, not by memory
    /// contents: two routes to equal memory are two logs and two points.
    /// The entry holds the log, so its address is not reused while keyed.
    static PENDING_POINTS: std::cell::RefCell<
        std::collections::HashMap<(Option<ProgramPointId>, usize), (Arc<StepLog>, PathLink)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The point after `path` that the steps in `steps` reach, with `memory`.
fn pending_point(path: &PathLink, steps: &Arc<StepLog>, memory: &SharedMemory) -> PathLink {
    let key = (path.id(), Arc::as_ptr(steps) as usize);
    PENDING_POINTS.with(|points| {
        points
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| {
                (
                    steps.clone(),
                    path.after(memory.clone(), Some(steps.clone())),
                )
            })
            .1
            .clone()
    })
}

impl PartialEq for ProgramPoint {
    fn eq(&self, other: &Self) -> bool {
        self.memory == other.memory
    }
}

impl Eq for ProgramPoint {}

impl std::hash::Hash for ProgramPoint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.memory.hash(state);
    }
}

impl PartialOrd for ProgramPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProgramPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.memory.cmp(&other.memory)
    }
}

impl ProgramPoint {
    /// A point built from a bare memory state, with no place on a path.
    pub fn at(memory: &SharedMemory) -> Self {
        Self {
            memory: memory.clone(),
            path: PathLink::default(),
        }
    }

    /// The point a `Memory` value stands at, interning it first. Callers
    /// that already hold an interned state use [`ProgramPoint::at`].
    pub(crate) fn of_memory(memory: &Memory) -> Self {
        Self::at(&intern_memory(memory.clone()))
    }

    /// The point a state stands at on its path.
    #[cfg_attr(not(test), allow(dead_code))]
    /// The point a state with `memory` stands at, `path` being the last
    /// point it reached. Steps the state has taken since, still in the
    /// memory's log, are a point of their own after that one, so the point
    /// handed out holds the memory it names.
    pub(super) fn of_state(memory: &Memory, path: &PathLink) -> Self {
        let shared = intern_memory_ref(memory);
        let path = match &memory.pending_steps {
            Some(steps) if path.memory() != Some(&shared) => pending_point(path, steps, &shared),
            _ => path.clone(),
        };
        Self {
            memory: shared,
            path,
        }
    }

    pub(crate) fn shared_memory(&self) -> &SharedMemory {
        &self.memory
    }

    /// Where on its path this point is.
    pub(super) fn path_link(&self) -> &PathLink {
        &self.path
    }

    /// The interned memory state this point stands for, by value.
    pub(crate) fn into_shared_memory(self) -> SharedMemory {
        self.memory
    }

    pub(crate) fn memory(&self) -> &Memory {
        self.memory.memory()
    }

    /// This point's identity on its path, or none for a point built from a
    /// bare memory state.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn id(&self) -> Option<ProgramPointId> {
        self.path.id()
    }

    /// The identities of the points this one was reached from.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn predecessor_ids(&self) -> Vec<ProgramPointId> {
        self.path.predecessor_ids()
    }

    /// True when this point is later in the recorded history than `other`.
    /// Memory state ids strictly increase along derivation edges, so comparing
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

    fn memory_holding(value: u32) -> Memory {
        let block: PointerBlock = "local:slot".into();
        let slot = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        Memory::new()
            .with_block(block, 4)
            .store(slot, ProgramValue::Int32(MachineTerm::constant(value)))
    }

    fn slot() -> Pointer {
        Pointer {
            block: "local:slot".into(),
            offset: PointerOffsetTerm::Constant(0),
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

    /// A path is a chain of points; dropping a long one must not recurse
    /// once per link.
    #[test]
    fn a_long_path_drops_without_recursing_per_point() {
        let memory = intern_memory(Memory::new());
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
}
