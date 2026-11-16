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

use super::{Memory, SharedMemory, intern_memory, intern_memory_ref};

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

#[derive(Debug)]
struct PointNode {
    id: ProgramPointId,
    /// The points this one was reached from on its path: one after an
    /// ordinary transition, two after a branch join, none at the start.
    predecessors: Box<[PathLink]>,
}

impl Drop for PointNode {
    /// A long path is a long chain; dropping it one link at a time keeps the
    /// stack flat however many transitions the path made.
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.predecessors).into_vec();
        while let Some(PathLink(node)) = pending.pop() {
            if let Some(node) = node
                && let Ok(mut node) = Arc::try_unwrap(node)
            {
                pending.extend(std::mem::take(&mut node.predecessors).into_vec());
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
    /// A new point reached from this one.
    pub(crate) fn after(&self) -> Self {
        Self::reached_from(Box::new([self.clone()]))
    }

    /// A new point where two arms rejoin.
    pub(crate) fn joining(left: &Self, right: &Self) -> Self {
        Self::reached_from(Box::new([left.clone(), right.clone()]))
    }

    fn reached_from(predecessors: Box<[PathLink]>) -> Self {
        let predecessors = predecessors
            .into_vec()
            .into_iter()
            .filter(|point| point.0.is_some())
            .collect();
        Self(Some(Arc::new(PointNode {
            id: ProgramPointId::fresh(),
            predecessors,
        })))
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
    pub(super) fn of_state(memory: &Memory, path: &PathLink) -> Self {
        Self {
            memory: intern_memory_ref(memory),
            path: path.clone(),
        }
    }

    pub(crate) fn shared_memory(&self) -> &SharedMemory {
        &self.memory
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

    /// A path is a chain of points; dropping a long one must not recurse
    /// once per link.
    #[test]
    fn a_long_path_drops_without_recursing_per_point() {
        let mut point = PathLink::default();
        for _ in 0..200_000 {
            point = point.after();
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
        joined.join_program_points(&left, &right);
        assert_eq!(
            joined.program_point().predecessor_ids(),
            vec![
                left.program_point().id().unwrap(),
                right.program_point().id().unwrap()
            ]
        );
    }
}
