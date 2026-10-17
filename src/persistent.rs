use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static NODE_ALLOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static PERSISTENT_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn record_persistent_work(units: usize) {
    PERSISTENT_WORK.with(|work| work.set(work.get().saturating_add(units)));
}

#[cfg(not(test))]
pub(crate) fn record_persistent_work(_units: usize) {}

/// A persistent AVL map. Clones share the complete root; updating one key
/// copies only the search path and any rotation nodes.
#[derive(Clone)]
pub(crate) struct PersistentMap<K, V> {
    root: Option<Arc<Node<K, V>>>,
    len: usize,
}

struct Node<K, V> {
    key: Arc<K>,
    value: Arc<V>,
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
    height: u16,
}

impl<K, V> Default for PersistentMap<K, V> {
    fn default() -> Self {
        Self { root: None, len: 0 }
    }
}

impl<K: Ord, V> PersistentMap<K, V> {
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub(crate) fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            record_persistent_work(1);
            match key.cmp(current.key.as_ref().borrow()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return Some(current.value.as_ref()),
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        None
    }

    pub(crate) fn get_key_value<Q: Ord + ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
    {
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            record_persistent_work(1);
            match key.cmp(current.key.as_ref().borrow()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return Some((current.key.as_ref(), current.value.as_ref())),
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        None
    }

    pub(crate) fn contains_key<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        self.get(key).is_some()
    }

    /// Returns the greatest entry whose key is strictly less than `key`.
    pub(crate) fn get_less_than(&self, key: &K) -> Option<(&K, &V)> {
        let mut node = self.root.as_deref();
        let mut candidate = None;
        while let Some(current) = node {
            record_persistent_work(1);
            match key.cmp(current.key.as_ref()) {
                Ordering::Less | Ordering::Equal => node = current.left.as_deref(),
                Ordering::Greater => {
                    candidate = Some((current.key.as_ref(), current.value.as_ref()));
                    node = current.right.as_deref();
                }
            }
        }
        candidate
    }

    /// Returns the least entry whose key is strictly greater than `key`.
    pub(crate) fn get_greater_than(&self, key: &K) -> Option<(&K, &V)> {
        let mut node = self.root.as_deref();
        let mut candidate = None;
        while let Some(current) = node {
            record_persistent_work(1);
            match key.cmp(current.key.as_ref()) {
                Ordering::Less => {
                    candidate = Some((current.key.as_ref(), current.value.as_ref()));
                    node = current.left.as_deref();
                }
                Ordering::Equal | Ordering::Greater => node = current.right.as_deref(),
            }
        }
        candidate
    }

    pub(crate) fn with_inserted(&self, key: K, value: V) -> Self {
        let (root, inserted) = insert_node(self.root.as_ref(), Arc::new(key), Arc::new(value));
        Self {
            root: Some(root),
            len: self.len + usize::from(inserted),
        }
    }

    /// Update one binding while retaining structural sharing with cloned maps.
    pub(crate) fn insert(&mut self, key: K, value: V) {
        *self = self.with_inserted(key, value);
    }

    pub(crate) fn remove(&mut self, key: &K) {
        *self = self.without_key(key);
    }

    pub(crate) fn without_key(&self, key: &K) -> Self {
        let (root, removed) = remove_node(self.root.as_ref(), key);
        Self {
            root,
            len: self.len - usize::from(removed),
        }
    }

    pub(crate) fn iter(&self) -> PersistentMapIter<'_, K, V> {
        PersistentMapIter::new(self.root.as_deref(), self.len)
    }

    pub(crate) fn values(&self) -> impl DoubleEndedIterator<Item = &V> + ExactSizeIterator {
        self.iter().map(|(_, value)| value)
    }

    pub(crate) fn keys(&self) -> impl DoubleEndedIterator<Item = &K> + ExactSizeIterator {
        self.iter().map(|(key, _)| key)
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, key: &K) -> usize {
        let mut comparisons = 0;
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            comparisons += 1;
            match key.cmp(current.key.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return comparisons,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        comparisons
    }

    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }

    /// The entries on which `self` and `other` differ, in ascending key
    /// order: a key with its value on each side, `None` where that side
    /// lacks it.
    ///
    /// Subtrees and values the two maps share are skipped by identity, so
    /// for maps derived from one another, or from one base, by `k` updates
    /// the walk is proportional to the `k` changed paths, not to the maps.
    pub(crate) fn diff<'a>(&'a self, other: &'a Self) -> PersistentMapDiff<'a, K, V>
    where
        V: PartialEq,
    {
        PersistentMapDiff {
            left: self.root.iter().map(DiffItem::Tree).collect(),
            right: other.root.iter().map(DiffItem::Tree).collect(),
        }
    }
}

/// One side of a [`PersistentMap::diff`] walk: a stack whose top is the
/// next unvisited part of the map in key order, either a whole subtree or
/// one entry.
enum DiffItem<'a, K, V> {
    Tree(&'a Arc<Node<K, V>>),
    Entry(&'a Node<K, V>),
}

pub(crate) struct PersistentMapDiff<'a, K, V> {
    left: Vec<DiffItem<'a, K, V>>,
    right: Vec<DiffItem<'a, K, V>>,
}

fn expand<K, V>(stack: &mut Vec<DiffItem<'_, K, V>>) {
    let Some(DiffItem::Tree(node)) = stack.pop() else {
        unreachable!("only a subtree expands")
    };
    record_persistent_work(1);
    if let Some(right) = &node.right {
        stack.push(DiffItem::Tree(right));
    }
    stack.push(DiffItem::Entry(node));
    if let Some(left) = &node.left {
        stack.push(DiffItem::Tree(left));
    }
}

impl<'a, K: Ord, V: PartialEq> Iterator for PersistentMapDiff<'a, K, V> {
    type Item = (&'a K, Option<&'a V>, Option<&'a V>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match (self.left.last(), self.right.last()) {
                (None, None) => return None,
                // Both walks stand at one shared subtree: it holds the same
                // entries on both sides at the same position.
                (Some(DiffItem::Tree(left)), Some(DiffItem::Tree(right)))
                    if Arc::ptr_eq(left, right) =>
                {
                    self.left.pop();
                    self.right.pop();
                }
                // Open the taller subtree first, so a subtree the other side
                // shares comes to the top on both.
                (Some(DiffItem::Tree(left)), Some(DiffItem::Tree(right))) => {
                    let (left_height, right_height) = (left.height, right.height);
                    if left_height >= right_height {
                        expand(&mut self.left);
                    }
                    if right_height >= left_height {
                        expand(&mut self.right);
                    }
                }
                (Some(DiffItem::Tree(_)), _) => expand(&mut self.left),
                (_, Some(DiffItem::Tree(_))) => expand(&mut self.right),
                (Some(DiffItem::Entry(left)), Some(DiffItem::Entry(right))) => {
                    let (left, right) = (*left, *right);
                    match left.key.as_ref().cmp(right.key.as_ref()) {
                        Ordering::Less => {
                            self.left.pop();
                            return Some((left.key.as_ref(), Some(left.value.as_ref()), None));
                        }
                        Ordering::Greater => {
                            self.right.pop();
                            return Some((right.key.as_ref(), None, Some(right.value.as_ref())));
                        }
                        Ordering::Equal => {
                            self.left.pop();
                            self.right.pop();
                            if !Arc::ptr_eq(&left.value, &right.value) && left.value != right.value
                            {
                                return Some((
                                    left.key.as_ref(),
                                    Some(left.value.as_ref()),
                                    Some(right.value.as_ref()),
                                ));
                            }
                        }
                    }
                }
                (Some(DiffItem::Entry(left)), None) => {
                    let left = *left;
                    self.left.pop();
                    return Some((left.key.as_ref(), Some(left.value.as_ref()), None));
                }
                (None, Some(DiffItem::Entry(right))) => {
                    let right = *right;
                    self.right.pop();
                    return Some((right.key.as_ref(), None, Some(right.value.as_ref())));
                }
            }
        }
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for PersistentMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        iter.into_iter().fold(Self::default(), |map, (key, value)| {
            map.with_inserted(key, value)
        })
    }
}

impl<K: Ord, V> Extend<(K, V)> for PersistentMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a PersistentMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = PersistentMapIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<K: Ord + PartialEq, V: PartialEq> PartialEq for PersistentMap<K, V> {
    /// O(1) for maps sharing a root (a clone, or a context compared with
    /// itself through a fact-context memo); otherwise proportional to the
    /// parts the two maps do not share (see [`PersistentMap::diff`]).
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && (self.shares_root_with(other) || self.diff(other).next().is_none())
    }
}

impl<K: Ord + Eq, V: Eq> Eq for PersistentMap<K, V> {}

impl<K: Ord, V: PartialOrd> PartialOrd for PersistentMap<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.shares_root_with(other) {
            return Some(Ordering::Equal);
        }
        self.iter().partial_cmp(other.iter())
    }
}

/// In key order, as `BTreeMap`'s order: entries compared lexicographically.
impl<K: Ord, V: Ord> Ord for PersistentMap<K, V> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.shares_root_with(other) {
            return Ordering::Equal;
        }
        self.iter().cmp(other.iter())
    }
}

/// As `BTreeMap` hashes: the length, then every entry in key order.
impl<K: Ord + std::hash::Hash, V: std::hash::Hash> std::hash::Hash for PersistentMap<K, V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.len);
        for (key, value) in self.iter() {
            key.hash(state);
            value.hash(state);
        }
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for PersistentMap<K, V> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

pub(crate) struct PersistentMapIter<'a, K, V> {
    front: Vec<&'a Node<K, V>>,
    back: Vec<&'a Node<K, V>>,
    remaining: usize,
}

impl<'a, K, V> PersistentMapIter<'a, K, V> {
    fn new(root: Option<&'a Node<K, V>>, remaining: usize) -> Self {
        let mut iter = Self {
            front: Vec::new(),
            back: Vec::new(),
            remaining,
        };
        iter.push_front(root);
        iter.push_back(root);
        iter
    }

    fn push_front(&mut self, mut node: Option<&'a Node<K, V>>) {
        while let Some(current) = node {
            self.front.push(current);
            node = current.left.as_deref();
        }
    }

    fn push_back(&mut self, mut node: Option<&'a Node<K, V>>) {
        while let Some(current) = node {
            self.back.push(current);
            node = current.right.as_deref();
        }
    }
}

impl<'a, K, V> Iterator for PersistentMapIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let node = self.front.pop()?;
        self.push_front(node.right.as_deref());
        Some((node.key.as_ref(), node.value.as_ref()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> DoubleEndedIterator for PersistentMapIter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let node = self.back.pop()?;
        self.push_back(node.left.as_deref());
        Some((node.key.as_ref(), node.value.as_ref()))
    }
}

impl<K, V> ExactSizeIterator for PersistentMapIter<'_, K, V> {}

#[derive(Clone)]
pub(crate) struct PersistentSet<T> {
    map: PersistentMap<T, ()>,
}

impl<T: Ord + PartialEq> PartialEq for PersistentSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<T: Ord + Eq> Eq for PersistentSet<T> {}

impl<T: Ord + fmt::Debug> fmt::Debug for PersistentSet<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.map.fmt(formatter)
    }
}

impl<T> Default for PersistentSet<T> {
    fn default() -> Self {
        Self {
            map: PersistentMap::default(),
        }
    }
}

impl<T: Ord> PersistentSet<T> {
    pub(crate) fn with_value(&self, value: T) -> Self {
        Self {
            map: self.map.with_inserted(value, ()),
        }
    }

    pub(crate) fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.get(value).is_some()
    }

    pub(crate) fn without_value(&self, value: &T) -> Self {
        Self {
            map: self.map.without_key(value),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    pub(crate) fn iter(&self) -> impl DoubleEndedIterator<Item = &T> + ExactSizeIterator {
        self.map.keys()
    }

    /// Own the shared root; visiting the first value does not collect the set.
    pub(crate) fn owned_values(&self) -> OwnedSetValues<T> {
        OwnedSetValues {
            next: self.map.root.clone(),
            stack: Vec::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, value: &T) -> usize {
        self.map.lookup_comparisons(value)
    }

    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        self.map.shares_root_with(&other.map)
    }
}

pub(crate) struct OwnedSetValues<T> {
    next: Option<Arc<Node<T, ()>>>,
    stack: Vec<Arc<Node<T, ()>>>,
}
impl<T: Clone> Iterator for OwnedSetValues<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        while let Some(node) = self.next.take() {
            record_persistent_work(1);
            self.next = node.left.clone();
            self.stack.push(node);
        }
        let node = self.stack.pop()?;
        self.next = node.right.clone();
        Some((*node.key).clone())
    }
}

/// A node of a persistent AVL tree: its entry, its children and its height,
/// and how a node is built from them. A tree that keeps a summary per
/// subtree computes it in `make`, so the shared balancing code below serves
/// every such tree.
pub(crate) trait AvlNode: Sized {
    type Key;
    type Value;
    fn key(&self) -> &Arc<Self::Key>;
    fn value(&self) -> &Arc<Self::Value>;
    fn left(&self) -> &Option<Arc<Self>>;
    fn right(&self) -> &Option<Arc<Self>>;
    fn height(&self) -> u16;
    fn make(
        key: Arc<Self::Key>,
        value: Arc<Self::Value>,
        left: Option<Arc<Self>>,
        right: Option<Arc<Self>>,
    ) -> Arc<Self>;
}

impl<K, V> AvlNode for Node<K, V> {
    type Key = K;
    type Value = V;
    fn key(&self) -> &Arc<K> {
        &self.key
    }
    fn value(&self) -> &Arc<V> {
        &self.value
    }
    fn left(&self) -> &Option<Arc<Self>> {
        &self.left
    }
    fn right(&self) -> &Option<Arc<Self>> {
        &self.right
    }
    fn height(&self) -> u16 {
        self.height
    }
    fn make(
        key: Arc<K>,
        value: Arc<V>,
        left: Option<Arc<Self>>,
        right: Option<Arc<Self>>,
    ) -> Arc<Self> {
        make_node(key, value, left, right)
    }
}

pub(crate) fn node_height<N: AvlNode>(node: Option<&Arc<N>>) -> u16 {
    node.map_or(0, |node| node.height())
}

pub(crate) fn balance_node<N: AvlNode>(
    key: Arc<N::Key>,
    value: Arc<N::Value>,
    left: Option<Arc<N>>,
    right: Option<Arc<N>>,
) -> Arc<N> {
    let left_height = node_height(left.as_ref());
    let right_height = node_height(right.as_ref());
    if left_height > right_height + 1 {
        let left_node = left.as_ref().expect("left-heavy node has a left child");
        if node_height(left_node.left().as_ref()) >= node_height(left_node.right().as_ref()) {
            let new_right = N::make(key, value, left_node.right().clone(), right);
            return N::make(
                left_node.key().clone(),
                left_node.value().clone(),
                left_node.left().clone(),
                Some(new_right),
            );
        }
        let middle = left_node
            .right()
            .as_ref()
            .expect("left-right-heavy node has a middle child");
        let new_left = N::make(
            left_node.key().clone(),
            left_node.value().clone(),
            left_node.left().clone(),
            middle.left().clone(),
        );
        let new_right = N::make(key, value, middle.right().clone(), right);
        return N::make(
            middle.key().clone(),
            middle.value().clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    if right_height > left_height + 1 {
        let right_node = right.as_ref().expect("right-heavy node has a right child");
        if node_height(right_node.right().as_ref()) >= node_height(right_node.left().as_ref()) {
            let new_left = N::make(key, value, left, right_node.left().clone());
            return N::make(
                right_node.key().clone(),
                right_node.value().clone(),
                Some(new_left),
                right_node.right().clone(),
            );
        }
        let middle = right_node
            .left()
            .as_ref()
            .expect("right-left-heavy node has a middle child");
        let new_left = N::make(key, value, left, middle.left().clone());
        let new_right = N::make(
            right_node.key().clone(),
            right_node.value().clone(),
            middle.right().clone(),
            right_node.right().clone(),
        );
        return N::make(
            middle.key().clone(),
            middle.value().clone(),
            Some(new_left),
            Some(new_right),
        );
    }
    N::make(key, value, left, right)
}

pub(crate) fn insert_node<N: AvlNode<Key: Ord>>(
    node: Option<&Arc<N>>,
    key: Arc<N::Key>,
    value: Arc<N::Value>,
) -> (Arc<N>, bool) {
    record_persistent_work(1);
    let Some(node) = node else {
        return (N::make(key, value, None, None), true);
    };
    match key.as_ref().cmp(node.key().as_ref()) {
        Ordering::Less => {
            let (left, inserted) = insert_node(node.left().as_ref(), key, value);
            (
                balance_node(
                    node.key().clone(),
                    node.value().clone(),
                    Some(left),
                    node.right().clone(),
                ),
                inserted,
            )
        }
        Ordering::Equal => (
            N::make(key, value, node.left().clone(), node.right().clone()),
            false,
        ),
        Ordering::Greater => {
            let (right, inserted) = insert_node(node.right().as_ref(), key, value);
            (
                balance_node(
                    node.key().clone(),
                    node.value().clone(),
                    node.left().clone(),
                    Some(right),
                ),
                inserted,
            )
        }
    }
}

pub(crate) fn remove_leftmost<N: AvlNode<Key: Ord>>(
    node: &Arc<N>,
) -> (Option<Arc<N>>, Arc<N::Key>, Arc<N::Value>) {
    record_persistent_work(1);
    let Some(left) = node.left().as_ref() else {
        return (
            node.right().clone(),
            node.key().clone(),
            node.value().clone(),
        );
    };
    let (new_left, key, value) = remove_leftmost(left);
    (
        Some(balance_node(
            node.key().clone(),
            node.value().clone(),
            new_left,
            node.right().clone(),
        )),
        key,
        value,
    )
}

pub(crate) fn remove_node<N: AvlNode<Key: Ord>>(
    node: Option<&Arc<N>>,
    key: &N::Key,
) -> (Option<Arc<N>>, bool) {
    record_persistent_work(1);
    let Some(node) = node else {
        return (None, false);
    };
    match key.cmp(node.key().as_ref()) {
        Ordering::Less => {
            let (left, removed) = remove_node(node.left().as_ref(), key);
            if !removed {
                return (Some(node.clone()), false);
            }
            (
                Some(balance_node(
                    node.key().clone(),
                    node.value().clone(),
                    left,
                    node.right().clone(),
                )),
                true,
            )
        }
        Ordering::Greater => {
            let (right, removed) = remove_node(node.right().as_ref(), key);
            if !removed {
                return (Some(node.clone()), false);
            }
            (
                Some(balance_node(
                    node.key().clone(),
                    node.value().clone(),
                    node.left().clone(),
                    right,
                )),
                true,
            )
        }
        Ordering::Equal => match (node.left(), node.right()) {
            (None, _) => (node.right().clone(), true),
            (_, None) => (node.left().clone(), true),
            (Some(_), Some(right)) => {
                let (new_right, successor_key, successor_value) = remove_leftmost(right);
                (
                    Some(balance_node(
                        successor_key,
                        successor_value,
                        node.left().clone(),
                        new_right,
                    )),
                    true,
                )
            }
        },
    }
}

fn make_node<K, V>(
    key: Arc<K>,
    value: Arc<V>,
    left: Option<Arc<Node<K, V>>>,
    right: Option<Arc<Node<K, V>>>,
) -> Arc<Node<K, V>> {
    record_persistent_work(1);
    #[cfg(test)]
    NODE_ALLOCATIONS.with(|allocations| allocations.set(allocations.get() + 1));
    Arc::new(Node {
        key,
        value,
        height: 1 + node_height(left.as_ref()).max(node_height(right.as_ref())),
        left,
        right,
    })
}

#[cfg(test)]
pub(crate) fn persistent_node_allocations() -> usize {
    NODE_ALLOCATIONS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn measure_persistent_work<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = PERSISTENT_WORK.with(std::cell::Cell::get);
    let result = operation();
    let after = PERSISTENT_WORK.with(std::cell::Cell::get);
    (result, after.saturating_sub(before))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expected_diff(
        left: &std::collections::BTreeMap<u32, u32>,
        right: &std::collections::BTreeMap<u32, u32>,
    ) -> Vec<(u32, Option<u32>, Option<u32>)> {
        left.keys()
            .chain(right.keys())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .map(|key| (*key, left.get(key).copied(), right.get(key).copied()))
            .filter(|(_, left, right)| left != right)
            .collect()
    }

    #[test]
    fn diff_reports_exactly_the_differing_entries_of_derived_maps() {
        let mut base = PersistentMap::default();
        let mut base_model = std::collections::BTreeMap::new();
        for key in 0..200u32 {
            base.insert(key * 3, key);
            base_model.insert(key * 3, key);
        }
        // Each side derives from the base by its own inserts, overwrites
        // (some with an equal value) and removals, and both rebalance.
        let edit = |seed: u32| {
            let mut map = base.clone();
            let mut model = base_model.clone();
            for step in 0..40u32 {
                let key = (step * 37 + seed * 11) % 650;
                match (step + seed) % 4 {
                    0 => {
                        map.insert(key, step);
                        model.insert(key, step);
                    }
                    1 => {
                        map.remove(&key);
                        model.remove(&key);
                    }
                    2 => {
                        if let Some(value) = model.get(&key).copied() {
                            map.insert(key, value);
                        }
                    }
                    _ => {
                        map.insert(key + 1, seed);
                        model.insert(key + 1, seed);
                    }
                }
            }
            (map, model)
        };
        let (left, left_model) = edit(1);
        let (right, right_model) = edit(2);
        for (one, one_model, other, other_model) in [
            (&left, &left_model, &right, &right_model),
            (&base, &base_model, &left, &left_model),
            (
                &right,
                &right_model,
                &PersistentMap::default(),
                &Default::default(),
            ),
        ] {
            let actual = one
                .diff(other)
                .map(|(key, left, right)| (*key, left.copied(), right.copied()))
                .collect::<Vec<_>>();
            assert_eq!(actual, expected_diff(one_model, other_model));
            assert_eq!(one == other, one_model == other_model);
        }
        assert!(left.diff(&left.clone()).next().is_none());
    }

    #[test]
    fn diff_of_one_change_walks_one_path() {
        let mut base = PersistentMap::default();
        for key in 0..4096u32 {
            base.insert(key, key);
        }
        let changed = base.with_inserted(1234, 0);
        let (differences, work) =
            measure_persistent_work(|| base.diff(&changed).collect::<Vec<_>>().len());
        assert_eq!(differences, 1);
        // The changed path on each side, not the 4096 entries.
        assert!(work <= 4 * 13, "a one-key diff opened {work} subtrees");
    }

    #[test]
    fn persistent_map_forks_and_updates_scale_logarithmically() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut map = PersistentMap::default();
            for key in 0..size {
                map = map.with_inserted(key, key * 2);
            }
            let ancestor = map.clone();
            assert!(map.shares_root_with(&ancestor));

            let before = persistent_node_allocations();
            map = map.with_inserted(size, size * 2);
            let allocations = persistent_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 4 * logarithmic_height + 8;
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} map nodes (bound {allocation_bound})"
            );
            assert_eq!(ancestor.get(&size), None);
            assert_eq!(map.get(&size), Some(&(size * 2)));
            assert_eq!(
                map.iter()
                    .map(|(key, value)| (*key, *value))
                    .collect::<Vec<_>>(),
                (0..=size).map(|key| (key, key * 2)).collect::<Vec<_>>()
            );

            let before_update = persistent_node_allocations();
            let updated = map.with_inserted(size, 7);
            let update_allocations = persistent_node_allocations() - before_update;
            assert!(update_allocations <= allocation_bound);
            assert_eq!(map.get(&size), Some(&(size * 2)));
            assert_eq!(updated.get(&size), Some(&7));
        }
    }

    #[test]
    fn persistent_map_removal_preserves_ancestor_and_avl_order() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut map = PersistentMap::default();
            for key in 0..size {
                map = map.with_inserted(key, key * 2);
            }
            let ancestor = map.clone();
            let removed_key = size / 2;
            let before = persistent_node_allocations();
            map = map.without_key(&removed_key);
            let allocations = persistent_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 8 * logarithmic_height + 8;
            assert!(
                allocations <= allocation_bound,
                "size {size} removal allocated {allocations} nodes (bound {allocation_bound})"
            );
            assert_eq!(ancestor.get(&removed_key), Some(&(removed_key * 2)));
            assert_eq!(map.get(&removed_key), None);
            assert_eq!(ancestor.len(), size as usize);
            assert_eq!(map.len(), size as usize - 1);
            assert!(map.iter().map(|(key, _)| *key).is_sorted());

            let unchanged = map.without_key(&u32::MAX);
            assert!(unchanged.shares_root_with(&map));
            assert_eq!(unchanged.len(), map.len());
        }
    }
}
