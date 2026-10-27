//! The fact collections of a `PureFactContext`, with every full iteration
//! charged.
//!
//! A lookup, an insertion, or an identity check on these collections is an
//! indexed operation. Iterating one reads a collection that grows with the
//! path, which the fast part may not do (`docs/internals/verifier-design.md`).
//! Each element an iteration visits records one unit of deterministic work,
//! so a scan shows up in the work that scaling tests and tactic budgets
//! measure, wherever it is written. A scan that is not charged is invisible
//! to both.

use crate::persistent::PersistentMap;

/// An iterator that records one unit of deterministic work per element. In
/// test builds it also counts the elements visited under the source location
/// that started the iteration ([`scan_sites`]), so a scaling test that sees
/// work grow can name the scan.
pub(crate) struct ChargedIter<I> {
    inner: I,
    #[cfg(test)]
    site: &'static std::panic::Location<'static>,
}

impl<I> ChargedIter<I> {
    #[track_caller]
    fn new(inner: I) -> Self {
        Self {
            inner,
            #[cfg(test)]
            site: std::panic::Location::caller(),
        }
    }

    fn visit(&self) {
        crate::instrumentation::record_deterministic_work(1);
        #[cfg(test)]
        {
            SCAN_SITES.with(|sites| *sites.borrow_mut().entry(self.site).or_default() += 1);
        }
    }
}

#[cfg(test)]
thread_local! {
    static SCAN_SITES: std::cell::RefCell<
        std::collections::HashMap<&'static std::panic::Location<'static>, usize>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The fact-collection elements visited on this thread since the last call,
/// by the source location that started each iteration, most visited first.
#[cfg(test)]
pub(crate) fn take_scan_sites() -> Vec<(String, usize)> {
    let mut sites = SCAN_SITES
        .with(|sites| std::mem::take(&mut *sites.borrow_mut()))
        .into_iter()
        .map(|(site, visits)| (site.to_string(), visits))
        .collect::<Vec<_>>();
    sites.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(&right.0)));
    sites
}

impl<I: Iterator> Iterator for ChargedIter<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.inner.next()?;
        self.visit();
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<I: DoubleEndedIterator> DoubleEndedIterator for ChargedIter<I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let item = self.inner.next_back()?;
        self.visit();
        Some(item)
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for ChargedIter<I> {}

/// Diagnostic collection access cannot expose an unbounded iterator, even if
/// a caller accidentally supplies a context-sized limit.
pub(crate) const DIAGNOSTIC_FACT_LIMIT: usize = 32;

fn diagnostic_sample<I: DoubleEndedIterator>(
    mut entries: I,
    first: usize,
    last: usize,
) -> Vec<I::Item> {
    let first = first.min(DIAGNOSTIC_FACT_LIMIT);
    let last = last.min(DIAGNOSTIC_FACT_LIMIT - first);
    let mut sample: Vec<_> = entries.by_ref().take(first).collect();
    let mut tail: Vec<_> = entries.rev().take(last).collect();
    tail.reverse();
    sample.extend(tail);
    sample
}

/// A persistent map of facts whose iteration is charged per element.
#[derive(Clone)]
pub(crate) struct FactMap<K, V>(PersistentMap<K, V>);

impl<K: Ord + std::fmt::Debug, V: std::fmt::Debug> std::fmt::Debug for FactMap<K, V> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl<K, V> Default for FactMap<K, V> {
    fn default() -> Self {
        Self(PersistentMap::default())
    }
}

impl<K: Ord, V> FactMap<K, V> {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
    {
        self.0.get(key)
    }

    pub(crate) fn with_inserted(&self, key: K, value: V) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Self(self.0.with_inserted(key, value))
    }

    pub(crate) fn without_key(&self, key: &K) -> Self
    where
        K: Clone,
        V: Clone,
    {
        Self(self.0.without_key(key))
    }

    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        self.0.shares_root_with(&other.0)
    }

    /// Every entry, in key order, charged one unit each.
    #[track_caller]
    fn scan(&self) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        ChargedIter::new(self.0.iter())
    }

    /// At most 32 entries from the two ends, in index order, charged per visit.
    #[track_caller]
    pub(crate) fn diagnostic_sample(&self, first: usize, last: usize) -> Vec<(&K, &V)> {
        diagnostic_sample(self.scan(), first, last)
    }

    /// Every entry, for maintaining this context itself: rebuilding an
    /// index, recomputing an identity, a debug consistency check, copying
    /// the context whole. Diagnostics use bounded samples instead.
    /// Not for answering a query.
    #[track_caller]
    pub(crate) fn scan_for_upkeep(
        &self,
    ) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        self.scan()
    }

    /// Every entry, for a search that `click expand` replaces with explicit
    /// steps (`docs/concepts/smart-and-simple-tactics.md`). Fast code, which
    /// still runs after expansion, must not reach this.
    #[track_caller]
    pub(crate) fn scan_for_search(
        &self,
        _permission: &crate::SearchPermission,
    ) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        self.scan()
    }

    /// Every entry of a context that is itself a step's explicit input, such
    /// as the premises a certificate names. The work is the input's
    /// size, which the step's author wrote.
    #[track_caller]
    pub(crate) fn scan_explicit_input(
        &self,
    ) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        self.scan()
    }

    #[cfg(test)]
    #[track_caller]
    pub(crate) fn iter(&self) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        self.scan()
    }
}

impl<K: Ord + PartialEq, V: PartialEq> PartialEq for FactMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K: Ord + Eq, V: Eq> Eq for FactMap<K, V> {}

impl<K: Ord + Clone, V: Clone> FromIterator<(K, V)> for FactMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// A persistent set of facts whose iteration is charged per element.
#[derive(Clone, Debug)]
pub(crate) struct FactSet<T: Clone + Ord>(imbl::OrdSet<T>);

impl<T: Clone + Ord> Default for FactSet<T> {
    fn default() -> Self {
        Self(imbl::OrdSet::new())
    }
}

impl<T: Clone + Ord> FactSet<T> {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn contains(&self, value: &T) -> bool {
        self.0.contains(value)
    }

    pub(crate) fn insert(&mut self, value: T) -> Option<T> {
        self.0.insert(value)
    }

    pub(crate) fn remove(&mut self, value: &T) -> Option<T> {
        self.0.remove(value)
    }

    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }

    /// Every fact, in order, charged one unit each.
    #[track_caller]
    fn scan(&self) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        ChargedIter::new(self.0.iter())
    }

    /// At most 32 entries from the two ends, in index order, charged per visit.
    #[track_caller]
    pub(crate) fn diagnostic_sample(&self, first: usize, last: usize) -> Vec<&T> {
        diagnostic_sample(self.scan(), first, last)
    }

    /// Every fact, for maintaining this context itself; see
    /// [`FactMap::scan_for_upkeep`].
    #[track_caller]
    pub(crate) fn scan_for_upkeep(
        &self,
    ) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        self.scan()
    }

    /// Every fact, for a search `click expand` replaces; see
    /// [`FactMap::scan_for_search`].
    #[track_caller]
    pub(crate) fn scan_for_search(
        &self,
        _permission: &crate::SearchPermission,
    ) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        self.scan()
    }

    /// Every entry of a context that is itself a step's explicit input, such
    /// as the premises a certificate names; see [`FactMap::scan_explicit_input`]. The work is the input's
    /// size, which the step's author wrote.
    #[track_caller]
    pub(crate) fn scan_explicit_input(
        &self,
    ) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        self.scan()
    }

    // No `scan_unindexed`: fast code reads proposition facts only through
    // an index, and a new whole-set scan there does not compile.

    #[cfg(test)]
    #[track_caller]
    pub(crate) fn iter(
        &self,
    ) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        self.scan()
    }
}

impl<T: Clone + Ord> PartialEq for FactSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Clone + Ord> Eq for FactSet<T> {}

impl<T: Clone + Ord> FromIterator<T> for FactSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// A persistent set of context records whose whole-set iteration must be
/// named, like [`FactSet`]'s: the resource compositions and the derived
/// fact sets of a context. Charged one unit per element.
#[derive(Clone)]
pub(crate) struct ScanSet<T>(crate::persistent::PersistentSet<T>);

impl<T> Default for ScanSet<T> {
    fn default() -> Self {
        Self(crate::persistent::PersistentSet::default())
    }
}

impl<T: Ord + std::fmt::Debug> std::fmt::Debug for ScanSet<T> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl<T: Ord + PartialEq> PartialEq for ScanSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Ord + Eq> Eq for ScanSet<T> {}

impl<T: Ord> ScanSet<T> {
    pub(crate) fn with_value(&self, value: T) -> Self {
        Self(self.0.with_value(value))
    }

    pub(crate) fn without_value(&self, value: &T) -> Self {
        Self(self.0.without_value(value))
    }

    pub(crate) fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: std::borrow::Borrow<Q>,
    {
        self.0.contains(value)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn shares_root_with(&self, other: &Self) -> bool {
        self.0.shares_root_with(&other.0)
    }

    /// The elements only one of the two sets holds, walking only the paths
    /// where their persistent trees differ (`PersistentSet::diff`).
    pub(crate) fn diff<'a>(&'a self, other: &'a Self) -> impl Iterator<Item = (&'a T, bool)> + 'a {
        self.0.diff(&other.0)
    }

    #[track_caller]
    fn scan(&self) -> ChargedIter<impl DoubleEndedIterator<Item = &T> + ExactSizeIterator> {
        ChargedIter::new(self.0.iter())
    }

    /// Every element, for maintaining the context; see
    /// [`FactMap::scan_for_upkeep`].
    #[track_caller]
    pub(crate) fn scan_for_upkeep(
        &self,
    ) -> ChargedIter<impl DoubleEndedIterator<Item = &T> + ExactSizeIterator> {
        self.scan()
    }

    /// Every element of a step's explicit input; see
    /// [`FactMap::scan_explicit_input`].
    #[track_caller]
    pub(crate) fn scan_explicit_input(
        &self,
    ) -> ChargedIter<impl DoubleEndedIterator<Item = &T> + ExactSizeIterator> {
        self.scan()
    }

    /// Every element, for a search that expansion removes; see
    /// [`FactMap::scan_for_search`].
    #[track_caller]
    pub(crate) fn scan_for_search<'a>(
        &'a self,
        _permission: &crate::SearchPermission,
    ) -> ChargedIter<impl DoubleEndedIterator<Item = &'a T> + ExactSizeIterator + use<'a, T>> {
        self.scan()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Catches a fact collection whose full iteration stops charging work:
    /// every element an iteration visits is one unit, and a lookup is free.
    #[test]
    fn iterating_a_fact_collection_charges_each_element() {
        let map = (0..32u64).map(|key| (key, true)).collect::<FactMap<_, _>>();
        let set = (0..16u64).collect::<FactSet<_>>();
        take_scan_sites();
        let ((), lookups) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(map.get(&7), Some(&true));
            assert!(set.contains(&7));
        });
        assert_eq!(lookups, 0);
        let (visited, work) = crate::instrumentation::measure_deterministic_work(|| {
            map.scan_for_upkeep().count() + map.scan_explicit_input().count() + set.iter().count()
        });
        assert_eq!((visited, work), (80, 80));
        let sites = take_scan_sites();
        assert_eq!(sites.iter().map(|(_, visits)| visits).sum::<usize>(), 80);
        assert!(
            sites
                .iter()
                .all(|(site, _)| site.starts_with("src/kernel/fact_collections.rs")),
            "each scan is filed under the line that started it: {sites:?}"
        );
    }
}
