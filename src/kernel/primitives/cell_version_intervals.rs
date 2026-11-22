//! Persistent range assignments for concrete call write bounds. A fully
//! covered subtree is replaced in one operation, including on a fork.
use std::{ops::Range, sync::Arc};

#[derive(Clone, Debug, Default)]
pub(super) struct CellVersionIntervals<Value = u32> {
    earlier: Option<Arc<Node<Value>>>,
    // Keep the latest interval at the root so repeated writes to one range
    // replace it without copying a path through the interval tree.
    newest: Option<(Range<u32>, Value)>,
}

#[derive(Debug)]
enum Node<Value> {
    Written(Value),
    Split(Option<Arc<Node<Value>>>, Option<Arc<Node<Value>>>),
}

const COORDINATES: Range<u32> = 0..(1 << 31);

impl<Value: Copy + Ord> CellVersionIntervals<Value> {
    /// Assign a range. Versions are recorded in nondecreasing order. Unit
    /// values track which bytes were written without naming a version.
    pub(super) fn write(&mut self, range: Range<u32>, version: Value) {
        debug_assert!(range.start < range.end && range.end <= COORDINATES.end);
        crate::instrumentation::record_deterministic_work(1);
        if let Some((earlier, earlier_version)) = self.newest.replace((range.clone(), version))
            && !covers(&range, &earlier)
        {
            let written = Arc::new(Node::Written(earlier_version));
            self.earlier = assign(self.earlier.as_ref(), COORDINATES, &earlier, &written);
        }
    }

    /// The query spans at most one scalar, so it visits only its bounded
    /// number of byte paths.
    pub(super) fn latest(&self, range: Range<u32>) -> Option<Value> {
        debug_assert!(range.start < range.end && range.end <= COORDINATES.end);
        if let Some((newest, version)) = &self.newest {
            crate::instrumentation::record_deterministic_work(1);
            if !disjoint(newest, &range) {
                return Some(*version);
            }
        }
        latest(self.earlier.as_deref(), COORDINATES, &range)
    }
}

fn disjoint(left: &Range<u32>, right: &Range<u32>) -> bool {
    left.end <= right.start || right.end <= left.start
}

fn covers(outer: &Range<u32>, inner: &Range<u32>) -> bool {
    outer.start <= inner.start && inner.end <= outer.end
}

fn assign<Value>(
    node: Option<&Arc<Node<Value>>>,
    span: Range<u32>,
    write: &Range<u32>,
    written: &Arc<Node<Value>>,
) -> Option<Arc<Node<Value>>> {
    crate::instrumentation::record_deterministic_work(1);
    if disjoint(&span, write) {
        return node.cloned();
    }
    if covers(write, &span) {
        return Some(written.clone());
    }
    let (left, right) = match node.map(Arc::as_ref) {
        Some(Node::Split(left, right)) => (left.as_ref(), right.as_ref()),
        _ => (node, node),
    };
    let mid = span.start.midpoint(span.end);
    Some(Arc::new(Node::Split(
        assign(left, span.start..mid, write, written),
        assign(right, mid..span.end, write, written),
    )))
}

fn latest<Value: Copy + Ord>(
    node: Option<&Node<Value>>,
    span: Range<u32>,
    read: &Range<u32>,
) -> Option<Value> {
    let node = node?;
    crate::instrumentation::record_deterministic_work(1);
    if disjoint(&span, read) {
        return None;
    }
    match node {
        Node::Written(version) => Some(*version),
        Node::Split(left, right) => {
            let mid = span.start.midpoint(span.end);
            latest(left.as_deref(), span.start..mid, read).max(latest(
                right.as_deref(),
                mid..span.end,
                read,
            ))
        }
    }
}
