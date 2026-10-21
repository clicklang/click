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
            if KNOWN_SCAN_DEPTH.with(std::cell::Cell::get) > 0 {
                KNOWN_SCAN_VISITS.with(|visits| visits.set(visits.get() + 1));
            }
        }
    }
}

/// Marks a fast-part scan the smart-tactics issue already lists ("Fast-part
/// scans" in `issues/smart-tactics.md`), for as long as the returned guard
/// lives. It changes nothing a verification does. In test builds the
/// elements its iterations visit are counted apart
/// ([`take_known_scan_visits`]), so a scaling test can assert that nothing
/// *else* grows with unrelated facts while the listed scan is still being
/// fixed. A new scan has no marker and fails such a test; fixing a listed
/// scan removes its marker.
#[must_use]
pub(crate) fn known_scan(_issue_item: &'static str) -> KnownScan {
    #[cfg(test)]
    KNOWN_SCAN_DEPTH.with(|depth| depth.set(depth.get() + 1));
    KnownScan(())
}

/// The scope of one [`known_scan`].
pub(crate) struct KnownScan(());

impl Drop for KnownScan {
    fn drop(&mut self) {
        #[cfg(test)]
        KNOWN_SCAN_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

#[cfg(test)]
thread_local! {
    static KNOWN_SCAN_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static KNOWN_SCAN_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The elements visited inside [`known_scan`] scopes on this thread since
/// the last call.
#[cfg(test)]
pub(crate) fn take_known_scan_visits() -> usize {
    KNOWN_SCAN_VISITS.with(|visits| visits.replace(0))
}

/// The deterministic work `operation` records, less the elements visited by
/// scans the smart-tactics issue lists ([`known_scan`]).
#[cfg(test)]
pub(crate) fn measure_work_beyond_known_scans<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    take_known_scan_visits();
    let (result, work) = crate::instrumentation::measure_deterministic_work(operation);
    (result, work.saturating_sub(take_known_scan_visits()))
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

    /// The entries that differ between `self` and `other`. Shared subtrees
    /// are skipped, so the cost follows the differences, not the size; the
    /// caller charges each difference it reads.
    pub(crate) fn diff<'a>(
        &'a self,
        other: &'a Self,
    ) -> crate::persistent::PersistentMapDiff<'a, K, V>
    where
        V: PartialEq,
    {
        self.0.diff(&other.0)
    }

    /// Every entry, in key order, charged one unit each.
    #[track_caller]
    pub(crate) fn iter(&self) -> ChargedIter<crate::persistent::PersistentMapIter<'_, K, V>> {
        ChargedIter::new(self.0.iter())
    }

    /// Every key, in order, charged one unit each.
    #[track_caller]
    pub(crate) fn keys(
        &self,
    ) -> ChargedIter<impl DoubleEndedIterator<Item = &K> + ExactSizeIterator> {
        ChargedIter::new(self.0.keys())
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

impl<'a, K: Ord, V> IntoIterator for &'a FactMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = ChargedIter<crate::persistent::PersistentMapIter<'a, K, V>>;

    #[track_caller]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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
    pub(crate) fn iter(
        &self,
    ) -> ChargedIter<imbl::ordset::Iter<'_, T, imbl::shared_ptr::DefaultSharedPtr>> {
        ChargedIter::new(self.0.iter())
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

impl<'a, T: Clone + Ord> IntoIterator for &'a FactSet<T> {
    type Item = &'a T;
    type IntoIter = ChargedIter<imbl::ordset::Iter<'a, T, imbl::shared_ptr::DefaultSharedPtr>>;

    #[track_caller]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Catches a fact collection whose full iteration stops charging work:
    /// every element an iteration visits is one unit, a lookup is free, and
    /// only visits inside a `known_scan` scope are set apart.
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
            map.iter().count() + map.keys().count() + set.iter().count()
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
        let ((), beyond) = measure_work_beyond_known_scans(|| {
            let _scan = known_scan("test");
            assert_eq!(map.iter().count(), 32);
        });
        assert_eq!(beyond, 0);
    }
}
