//! Persistent interval lookup for the trusted kernel's paired resource index.
//!
//! The AVL tree is ordered by (start, occurrence) and each subtree retains its
//! maximum end. A covering-range query visits only output ranges and the paths
//! needed to find them; it never walks unrelated predecessors. Updates and
//! forks share roots, and deletions repair summaries on the copied search path.
use super::super::ResourceEntryId;
use super::AddressCoordinate;
use crate::persistent::record_persistent_work;
use std::cmp::Ordering;
use std::sync::Arc;

type Key = (AddressCoordinate, ResourceEntryId);
type Value = AddressCoordinate;
type Root = Option<Arc<Node>>;

#[derive(Clone, Debug, Default)]
pub(super) struct ReadIntervals {
    root: Root,
    len: usize,
}

#[derive(Debug)]
struct Node {
    key: Arc<Key>,
    value: Arc<Value>,
    max_end: Arc<Value>,
    left: Root,
    right: Root,
    height: u16,
}

impl ReadIntervals {
    pub(super) fn len(&self) -> usize {
        self.len
    }

    pub(super) fn insert(
        &mut self,
        start: AddressCoordinate,
        end: AddressCoordinate,
        entry: ResourceEntryId,
    ) {
        let (root, inserted) =
            insert_node(self.root.as_ref(), Arc::new((start, entry)), Arc::new(end));
        self.root = Some(root);
        self.len += usize::from(inserted);
    }

    pub(super) fn remove(&mut self, start: AddressCoordinate, entry: ResourceEntryId) {
        let (root, removed) = remove_node(self.root.as_ref(), &(start, entry));
        self.root = root;
        self.len -= usize::from(removed);
    }

    pub(super) fn covering(
        &self,
        start: &AddressCoordinate,
        end: &AddressCoordinate,
    ) -> CoveringIntervals {
        CoveringIntervals {
            pending: self.root.iter().cloned().collect(),
            start: start.clone(),
            end: end.clone(),
        }
    }

    /// Used only when a class merge shifts the smaller resource payload.
    pub(super) fn iter(
        &self,
    ) -> impl Iterator<Item = (&AddressCoordinate, &AddressCoordinate, ResourceEntryId)> {
        let mut stack = Vec::new();
        let mut current = self.root.as_deref();
        std::iter::from_fn(move || {
            while let Some(node) = current {
                record_persistent_work(1);
                stack.push(node);
                current = node.left.as_deref();
            }
            let node = stack.pop()?;
            current = node.right.as_deref();
            Some((&node.key.0, node.value.as_ref(), node.key.1))
        })
    }
}

/// Owns a shared root, so permission checking need not hold the cache lock.
/// Enumeration stops as soon as the caller accepts a readable occurrence.
pub(in crate::kernel::primitives) struct CoveringIntervals {
    pending: Vec<Arc<Node>>,
    start: AddressCoordinate,
    end: AddressCoordinate,
}

impl Iterator for CoveringIntervals {
    type Item = ResourceEntryId;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.pending.pop() {
            record_persistent_work(1);
            if node.max_end.as_ref() < &self.end {
                continue;
            }
            let starts_before = node.key.0 <= self.start;
            if starts_before && let Some(right) = &node.right {
                self.pending.push(right.clone());
            }
            if let Some(left) = &node.left {
                self.pending.push(left.clone());
            }
            if starts_before && node.value.as_ref() >= &self.end {
                return Some(node.key.1);
            }
        }
        None
    }
}

fn node_height(node: Option<&Arc<Node>>) -> u16 {
    node.map_or(0, |node| node.height)
}

fn make_node(
    key: Arc<Key>,
    value: Arc<Value>,
    left: Option<Arc<Node>>,
    right: Option<Arc<Node>>,
) -> Arc<Node> {
    record_persistent_work(1);
    let mut max_end = value.clone();
    for child in [&left, &right].into_iter().flatten() {
        if child.max_end > max_end {
            max_end = child.max_end.clone();
        }
    }
    Arc::new(Node {
        max_end,
        key,
        value,
        height: 1 + node_height(left.as_ref()).max(node_height(right.as_ref())),
        left,
        right,
    })
}

fn balance_node(
    key: Arc<Key>,
    value: Arc<Value>,
    left: Option<Arc<Node>>,
    right: Option<Arc<Node>>,
) -> Arc<Node> {
    let left_height = node_height(left.as_ref());
    let right_height = node_height(right.as_ref());
    if left_height > right_height + 1 {
        let left_node = left.as_ref().expect("left-heavy node has a left child");
        if node_height(left_node.left.as_ref()) >= node_height(left_node.right.as_ref()) {
            let new_right = make_node(key, value, left_node.right.clone(), right);
            return make_node(
                left_node.key.clone(),
                left_node.value.clone(),
                left_node.left.clone(),
                Some(new_right),
            );
        }
        let middle = left_node
            .right
            .as_ref()
            .expect("left-right-heavy node has a middle child");
        let new_left = make_node(
            left_node.key.clone(),
            left_node.value.clone(),
            left_node.left.clone(),
            middle.left.clone(),
        );
        let new_right = make_node(key, value, middle.right.clone(), right);
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    if right_height > left_height + 1 {
        let right_node = right.as_ref().expect("right-heavy node has a right child");
        if node_height(right_node.right.as_ref()) >= node_height(right_node.left.as_ref()) {
            let new_left = make_node(key, value, left, right_node.left.clone());
            return make_node(
                right_node.key.clone(),
                right_node.value.clone(),
                Some(new_left),
                right_node.right.clone(),
            );
        }
        let middle = right_node
            .left
            .as_ref()
            .expect("right-left-heavy node has a middle child");
        let new_left = make_node(key, value, left, middle.left.clone());
        let new_right = make_node(
            right_node.key.clone(),
            right_node.value.clone(),
            middle.right.clone(),
            right_node.right.clone(),
        );
        return make_node(
            middle.key.clone(),
            middle.value.clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    make_node(key, value, left, right)
}

fn insert_node(node: Option<&Arc<Node>>, key: Arc<Key>, value: Arc<Value>) -> (Arc<Node>, bool) {
    record_persistent_work(1);
    let Some(node) = node else {
        return (make_node(key, value, None, None), true);
    };
    match key.as_ref().cmp(node.key.as_ref()) {
        Ordering::Less => {
            let (left, inserted) = insert_node(node.left.as_ref(), key, value);
            (
                balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    Some(left),
                    node.right.clone(),
                ),
                inserted,
            )
        }
        Ordering::Equal => (
            make_node(key, value, node.left.clone(), node.right.clone()),
            false,
        ),
        Ordering::Greater => {
            let (right, inserted) = insert_node(node.right.as_ref(), key, value);
            (
                balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    node.left.clone(),
                    Some(right),
                ),
                inserted,
            )
        }
    }
}

fn remove_leftmost(node: &Arc<Node>) -> (Option<Arc<Node>>, Arc<Key>, Arc<Value>) {
    record_persistent_work(1);
    let Some(left) = node.left.as_ref() else {
        return (node.right.clone(), node.key.clone(), node.value.clone());
    };
    let (new_left, key, value) = remove_leftmost(left);
    (
        Some(balance_node(
            node.key.clone(),
            node.value.clone(),
            new_left,
            node.right.clone(),
        )),
        key,
        value,
    )
}

fn remove_node(node: Option<&Arc<Node>>, key: &Key) -> (Option<Arc<Node>>, bool) {
    record_persistent_work(1);
    let Some(node) = node else {
        return (None, false);
    };
    match key.cmp(node.key.as_ref()) {
        Ordering::Less => {
            let (left, removed) = remove_node(node.left.as_ref(), key);
            if !removed {
                return (Some(node.clone()), false);
            }
            (
                Some(balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    left,
                    node.right.clone(),
                )),
                true,
            )
        }
        Ordering::Greater => {
            let (right, removed) = remove_node(node.right.as_ref(), key);
            if !removed {
                return (Some(node.clone()), false);
            }
            (
                Some(balance_node(
                    node.key.clone(),
                    node.value.clone(),
                    node.left.clone(),
                    right,
                )),
                true,
            )
        }
        Ordering::Equal => match (&node.left, &node.right) {
            (None, _) => (node.right.clone(), true),
            (_, None) => (node.left.clone(), true),
            (Some(_), Some(right)) => {
                let (new_right, successor_key, successor_value) = remove_leftmost(right);
                (
                    Some(balance_node(
                        successor_key,
                        successor_value,
                        node.left.clone(),
                        new_right,
                    )),
                    true,
                )
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::super::AffineOffset;
    use super::*;
    use std::collections::BTreeMap;

    fn coordinate(value: i128) -> AddressCoordinate {
        AddressCoordinate(AffineOffset::constant(value))
    }

    fn validate(node: Option<&Node>) -> (u16, Option<AddressCoordinate>) {
        let Some(node) = node else { return (0, None) };
        let (left_height, left_max) = validate(node.left.as_deref());
        let (right_height, right_max) = validate(node.right.as_deref());
        assert!(left_height.abs_diff(right_height) <= 1);
        assert_eq!(node.height, 1 + left_height.max(right_height));
        let max_end = [Some(node.value.as_ref().clone()), left_max, right_max]
            .into_iter()
            .flatten()
            .max()
            .unwrap();
        assert_eq!(node.max_end.as_ref(), &max_end);
        (node.height, Some(max_end))
    }

    #[test]
    fn interval_updates_match_an_independent_covering_model() {
        let mut intervals = ReadIntervals::default();
        let mut model = BTreeMap::new();
        let mut seed = 17_u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            seed
        };
        for step in 0..1200 {
            let entry = next() % 256;
            let start = i128::from(entry) - 128;
            if next().is_multiple_of(3) {
                intervals.remove(coordinate(start), entry);
                model.remove(&(start, entry));
            } else {
                let end = start + i128::from(next() % 200 + 1);
                intervals.insert(coordinate(start), coordinate(end), entry);
                model.insert((start, entry), end);
            }
            assert_eq!(intervals.len(), model.len());
            validate(intervals.root.as_deref());
            let start = i128::from(next() % 512) - 256;
            let end = start + i128::from(next() % 64);
            let expected = model
                .iter()
                .filter_map(|((range_start, entry), range_end)| {
                    (*range_start <= start && *range_end >= end).then_some(*entry)
                })
                .collect::<std::collections::BTreeSet<_>>();
            let actual = intervals
                .covering(&coordinate(start), &coordinate(end))
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(actual, expected, "step {step}");
        }
        let snapshot = intervals.clone();
        for (start, entry) in model.keys() {
            intervals.remove(coordinate(*start), *entry);
            validate(intervals.root.as_deref());
        }
        assert_eq!(intervals.len(), 0);
        assert!(intervals.root.is_none());
        assert_eq!(snapshot.len(), model.len());
        assert_eq!(snapshot.iter().count(), model.len());
    }
}
