//! Where an execution path is.
//!
//! A [`crate::kernel::resource_tracker::ProgramPoint`] is a memory snapshot,
//! and snapshots are interned by content, so two paths that reach equal
//! memory share one snapshot and one recorded history. A [`ReachedPoint`] is
//! the place itself: each memory transition on a path mints a fresh one,
//! linked to the point it came from, so two paths are two chains whatever
//! their memories hold.
//!
//! Nothing reads these yet. They are recorded alongside the snapshots so that
//! naming and the version walk can move onto them.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

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
#[cfg_attr(not(test), allow(dead_code))]
struct PointNode {
    id: ProgramPointId,
    /// The points this one was reached from on its path: one after an
    /// ordinary transition, two after a branch join, none at the start.
    predecessors: Box<[ReachedPoint]>,
}

impl Drop for PointNode {
    /// A long path is a long chain; dropping it one link at a time keeps the
    /// stack flat however many transitions the path made.
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.predecessors).into_vec();
        while let Some(ReachedPoint(node)) = pending.pop() {
            if let Some(node) = node
                && let Ok(mut node) = Arc::try_unwrap(node)
            {
                pending.extend(std::mem::take(&mut node.predecessors).into_vec());
            }
        }
    }
}

/// The point an execution state stands at, or none before the state's first
/// memory transition.
///
/// It is not part of the state's equality, hashing or order: two states are
/// equal when they hold the same things, wherever each was reached.
#[derive(Clone, Debug, Default)]
pub(crate) struct ReachedPoint(Option<Arc<PointNode>>);

impl ReachedPoint {
    /// A new point reached from this one.
    pub(crate) fn after(&self) -> Self {
        Self::reached_from(Box::new([self.clone()]))
    }

    /// A new point where two arms rejoin.
    pub(crate) fn joining(left: &Self, right: &Self) -> Self {
        Self::reached_from(Box::new([left.clone(), right.clone()]))
    }

    fn reached_from(predecessors: Box<[ReachedPoint]>) -> Self {
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

    #[cfg_attr(not(test), allow(dead_code))]
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

impl PartialEq for ReachedPoint {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for ReachedPoint {}

impl std::hash::Hash for ReachedPoint {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl PartialOrd for ReachedPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ReachedPoint {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;
    use super::ReachedPoint;

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
        let mut point = ReachedPoint::default();
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
        assert_ne!(left.reached_point().id(), right.reached_point().id());
        assert_eq!(
            left.reached_point().predecessor_ids(),
            vec![left_mid.reached_point().id().unwrap()]
        );
        assert_eq!(
            right.reached_point().predecessor_ids(),
            vec![right_mid.reached_point().id().unwrap()]
        );

        let mut joined = left.clone();
        joined.join_reached_points(&left, &right);
        assert_eq!(
            joined.reached_point().predecessor_ids(),
            vec![
                left.reached_point().id().unwrap(),
                right.reached_point().id().unwrap()
            ]
        );
    }
}
