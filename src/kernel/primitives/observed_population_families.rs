//! The resource families a proof has observed. Authority loan classification
//! reads these markers to decide whether a family's population is visible at
//! a call; they record no count and grant no authority.
use super::*;

/// One pointer in CState, so the common empty set costs no allocation and
/// unchanged sets compare by identity.
#[derive(Clone, Default)]
pub(crate) struct ObservedPopulationFamilies(Option<Arc<BTreeSet<String>>>);

impl ObservedPopulationFamilies {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.as_ref().is_none_or(|families| families.is_empty())
    }

    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => self.is_empty() && other.is_empty(),
        }
    }

    pub(crate) fn contains(&self, name: &str) -> bool {
        self.0
            .as_ref()
            .is_some_and(|families| families.contains(name))
    }

    pub(crate) fn insert(&mut self, name: String) {
        if !self.contains(&name) {
            Arc::make_mut(self.0.get_or_insert_with(Default::default)).insert(name);
        }
    }

    fn families(&self) -> impl Iterator<Item = &String> {
        self.0.iter().flat_map(|families| families.iter())
    }
}

impl PartialEq for ObservedPopulationFamilies {
    fn eq(&self, other: &Self) -> bool {
        self.shares_storage_with(other) || self.families().eq(other.families())
    }
}
impl Eq for ObservedPopulationFamilies {}
impl Hash for ObservedPopulationFamilies {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        for family in self.families() {
            family.hash(hasher);
        }
    }
}
impl Ord for ObservedPopulationFamilies {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.shares_storage_with(other) {
            std::cmp::Ordering::Equal
        } else {
            self.families().cmp(other.families())
        }
    }
}
impl PartialOrd for ObservedPopulationFamilies {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl std::fmt::Debug for ObservedPopulationFamilies {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.families()).finish()
    }
}
